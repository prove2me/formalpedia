-- Prove2me | solution 1 for BraidsLinksMCG.pureBraid_forget_section
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T19:38:39.520444+00:00
-- url     : https://prove2.me/submissions/8e457aa8-7d8a-4e56-8143-a9a2543303e3

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

namespace SectSol

variable (n : ℕ)

/-- A real coordinate strictly to the right of every point of the configuration,
which takes the value `n+1` at the base configuration. -/
noncomputable def newRe (p : Fin n → ℂ) : ℝ :=
  (n : ℝ) + 1 + ∑ i, max ((p i).re - (n : ℝ)) 0

lemma newRe_gt (p : Fin n → ℂ) (j : Fin n) : (p j).re < newRe n p := by
  have h1 : ∀ i : Fin n, 0 ≤ max ((p i).re - (n : ℝ)) 0 := fun i => le_max_right _ _
  have h2 : max ((p j).re - (n : ℝ)) 0 ≤ ∑ i, max ((p i).re - (n : ℝ)) 0 :=
    Finset.single_le_sum (fun i _ => h1 i) (Finset.mem_univ j)
  rcases le_or_gt ((p j).re) (n : ℝ) with h | h
  · have hs : (0 : ℝ) ≤ ∑ i, max ((p i).re - (n : ℝ)) 0 :=
      Finset.sum_nonneg (fun i _ => h1 i)
    unfold newRe; linarith
  · have hm : max ((p j).re - (n : ℝ)) 0 = (p j).re - (n : ℝ) := max_eq_left (by linarith)
    rw [hm] at h2
    unfold newRe; linarith

lemma continuous_newRe : Continuous (fun p : OrderedConfig n => newRe n p.1) := by
  unfold newRe
  refine continuous_const.add (continuous_finset_sum _ fun i _ => ?_)
  exact ((Complex.continuous_re.comp ((continuous_apply i).comp continuous_subtype_val)).sub
    continuous_const).max continuous_const

/-- The configuration with one extra point added to the right of all the others. -/
noncomputable def sectFun (p : OrderedConfig n) : Fin (n + 1) → ℂ :=
  Fin.snoc p.1 ((newRe n p.1 : ℝ) : ℂ)

lemma sectFun_injective (p : OrderedConfig n) : Function.Injective (sectFun n p) := by
  intro i j hij
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => rfl
    | cast b =>
      exfalso
      rw [sectFun, Fin.snoc_last, Fin.snoc_castSucc] at hij
      have := congrArg Complex.re hij
      simp only [Complex.ofReal_re] at this
      exact absurd this.symm (ne_of_lt (newRe_gt n p.1 b))
  | cast a =>
    induction j using Fin.lastCases with
    | last =>
      exfalso
      rw [sectFun, Fin.snoc_castSucc, Fin.snoc_last] at hij
      have := congrArg Complex.re hij
      simp only [Complex.ofReal_re] at this
      exact absurd this (ne_of_lt (newRe_gt n p.1 a))
    | cast b =>
      rw [sectFun, Fin.snoc_castSucc, Fin.snoc_castSucc] at hij
      exact congrArg Fin.castSucc (p.2 hij)

/-- Adding a strand far to the right, as a continuous map of configuration spaces. -/
noncomputable def sect : C(OrderedConfig n, OrderedConfig (n + 1)) where
  toFun p := ⟨sectFun n p, sectFun_injective n p⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    refine continuous_pi fun i => ?_
    induction i using Fin.lastCases with
    | last =>
      simp only [sectFun, Fin.snoc_last]
      exact Complex.continuous_ofReal.comp (continuous_newRe n)
    | cast a =>
      simp only [sectFun, Fin.snoc_castSucc]
      exact (continuous_apply a).comp continuous_subtype_val

lemma forget_sect (p : OrderedConfig n) : configForget n (sect n p) = p := by
  apply Subtype.ext
  funext i
  show sectFun n p i.castSucc = p.1 i
  simp [sectFun]

lemma sect_base : sect n (baseOrdered n) = baseOrdered (n + 1) := by
  apply Subtype.ext
  funext i
  induction i using Fin.lastCases with
  | last =>
    show sectFun n (baseOrdered n) (Fin.last n) = (baseOrdered (n + 1)).1 (Fin.last n)
    simp only [sectFun, Fin.snoc_last]
    have hsum : ∑ i : Fin n, max (((baseOrdered n).1 i).re - (n : ℝ)) 0 = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      have hre : ((baseOrdered n).1 i).re = ((i : ℕ) : ℝ) + 1 := by
        show (((i : ℕ) + 1 : ℂ)).re = _
        simp
      rw [hre]
      have : ((i : ℕ) : ℝ) + 1 - (n : ℝ) ≤ 0 := by
        have := i.isLt
        have : ((i : ℕ) : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast this
        linarith
      exact max_eq_right this
    rw [newRe, hsum]
    show ((((n : ℝ) + 1 + 0 : ℝ)) : ℂ) = (((Fin.last n : ℕ) : ℕ) + 1 : ℂ)
    push_cast
    ring
  | cast a =>
    show sectFun n (baseOrdered n) a.castSucc = (baseOrdered (n + 1)).1 a.castSucc
    simp only [sectFun, Fin.snoc_castSucc]
    show (((a : ℕ) + 1 : ℂ)) = (((a.castSucc : ℕ) : ℕ) + 1 : ℂ)
    norm_num

theorem forget_comp_sect :
    (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).comp
        (FundamentalGroup.mapOfEq (sect n) (sect_base n))
      = MonoidHom.id (PureBraidGroup n) := by
  refine MonoidHom.ext fun γ => ?_
  obtain ⟨Q, hQ⟩ := Quotient.exists_rep (FundamentalGroup.toPath γ)
  have hγ : FundamentalGroup.fromPath (⟦Q⟧ : Path.Homotopic.Quotient _ _) = γ :=
    congrArg FundamentalGroup.fromPath hQ
  rw [← hγ]
  show (FundamentalGroup.mapOfEq (configForget n) (configForget_base n))
      ((FundamentalGroup.mapOfEq (sect n) (sect_base n))
        (FundamentalGroup.fromPath (⟦Q⟧ : Path.Homotopic.Quotient _ _)))
    = FundamentalGroup.fromPath (⟦Q⟧ : Path.Homotopic.Quotient _ _)
  rw [FundamentalGroup.mapOfEq_apply, FundamentalGroup.mapOfEq_apply]
  have hpath :
      ((((Q.map (sect n).continuous).cast (sect_base n).symm (sect_base n).symm).map
        (configForget n).continuous).cast (configForget_base n).symm
          (configForget_base n).symm) = Q := by
    refine DFunLike.ext _ _ fun t => ?_
    exact forget_sect n (Q t)
  show (⟦(((Q.map (sect n).continuous).cast (sect_base n).symm (sect_base n).symm).map
        (configForget n).continuous).cast (configForget_base n).symm
          (configForget_base n).symm⟧ : Path.Homotopic.Quotient _ _) = ⟦Q⟧
  rw [hpath]

end SectSol


theorem _root_.solution (n : ℕ) :
    ∃ s : PureBraidGroup n →* PureBraidGroup (n + 1),
      (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).comp s =
        MonoidHom.id (PureBraidGroup n) :=
  ⟨FundamentalGroup.mapOfEq (SectSol.sect n) (SectSol.sect_base n), SectSol.forget_comp_sect n⟩

#print axioms solution
