-- Prove2me | solution 1 for BraidsLinksMCG.fadellNeuwirth_ker_le_range
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T06:57:50.58243+00:00
-- url     : https://prove2.me/submissions/16b5d58a-db6b-4268-93f9-884a90bc1ce3

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Theorems.Thm_BraidsLinksMCG_configForget_lift_path_homotopy

open BraidsLinksMCG

/-- A loop contained in the fibre is the inclusion of its last-coordinate loop. -/
private theorem fibre_loop_last_coordinate (n : ℕ)
    (δ : Path (baseOrdered (n + 1)) (baseOrdered (n + 1)))
    (hf : ∀ t, configForget n (δ t) = baseOrdered n) :
    ∃ z : Path (basePunctured n) (basePunctured n),
      (z.map (configIncl n).continuous).cast
        (configIncl_base n).symm (configIncl_base n).symm = δ := by
  have hcoord (t) (j : Fin n) : (δ t).1 j.castSucc = ((j : ℕ) + 1 : ℂ) :=
    congrArg (fun q : OrderedConfig n => q.1 j) (hf t)
  have havoid (t) : ∀ j : Fin n, (δ t).1 (Fin.last n) ≠ ((j : ℕ) + 1 : ℂ) := by
    intro j hj
    have he := (δ t).2 (hj.trans (hcoord t j).symm)
    have hv := congrArg Fin.val he
    have hjlt := j.isLt
    simp only [Fin.val_last, Fin.val_castSucc] at hv
    omega
  let z : Path (basePunctured n) (basePunctured n) :=
    { toFun := fun t => ⟨(δ t).1 (Fin.last n), havoid t⟩
      continuous_toFun :=
        ((continuous_apply (Fin.last n)).comp
          (continuous_subtype_val.comp δ.continuous)).subtype_mk havoid
      source' := by
        apply Subtype.ext
        change (δ 0).1 (Fin.last n) = ((n : ℕ) + 1 : ℂ)
        rw [δ.source]
        rfl
      target' := by
        apply Subtype.ext
        change (δ 1).1 (Fin.last n) = ((n : ℕ) + 1 : ℂ)
        rw [δ.target]
        rfl }
  refine ⟨z, ?_⟩
  apply DFunLike.ext
  intro t
  apply Subtype.ext
  funext i
  induction i using Fin.lastCases with
  | last =>
      change Fin.snoc (α := fun _ => ℂ) (fun k : Fin n => ((k : ℕ) + 1 : ℂ))
        ((δ t).1 (Fin.last n)) (Fin.last n) = (δ t).1 (Fin.last n)
      simp only [Fin.snoc_last]
  | cast j =>
      change Fin.snoc (α := fun _ => ℂ) (fun k : Fin n => ((k : ℕ) + 1 : ℂ))
        ((δ t).1 (Fin.last n)) j.castSucc = (δ t).1 j.castSucc
      simpa only [Fin.snoc_castSucc] using (hcoord t j).symm

/-- Reduce exactness to relative homotopy lifting, with explicit fibre coordinates. -/
theorem solution (n : ℕ) :
    (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).ker ≤
      (FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)).range := by
  intro x hx
  obtain ⟨γ, rfl⟩ := Path.Homotopic.Quotient.mk_surjective x
  change FundamentalGroup.mapOfEq (configForget n) (configForget_base n)
    (Path.Homotopic.Quotient.mk γ) = 1 at hx
  have hm : Path.Homotopic.Quotient.mk
      ((γ.map (configForget n).continuous).cast
        (configForget_base n).symm (configForget_base n).symm) =
      Path.Homotopic.Quotient.mk (Path.refl (baseOrdered n)) := by
    simpa only [FundamentalGroup.mapOfEq_apply, Path.Homotopic.Quotient.mk_cast,
      Path.Homotopic.Quotient.mk_map, Path.Homotopic.Quotient.mk_refl,
      FundamentalGroup.one_def] using hx
  obtain ⟨H⟩ := Path.Homotopic.Quotient.exact hm
  obtain ⟨δ, K, hK⟩ := configForget_lift_path_homotopy n γ
    (Path.refl (baseOrdered n)) H
  have hf : ∀ t, configForget n (δ t) = baseOrdered n := by
    intro t
    simpa using hK 1 t
  obtain ⟨z, hz⟩ := fibre_loop_last_coordinate n δ hf
  refine ⟨Path.Homotopic.Quotient.mk z, ?_⟩
  rw [FundamentalGroup.mapOfEq_apply, ← Path.Homotopic.Quotient.mk_map,
    ← Path.Homotopic.Quotient.mk_cast, hz]
  exact (Path.Homotopic.Quotient.eq.mpr ⟨K⟩).symm
