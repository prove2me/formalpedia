-- Prove2me | solution 2 for FredholmBanach.index_eq_zero_tfae
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-10T23:39:39.824245+00:00
-- url     : https://prove2.me/submissions/3517f4e2-7fb5-46f2-8d31-7dbe5c574c7a

import Definitions.Def_FredholmBanach_Setting
import Theorems.Thm_FredholmBanach_isFredholm_iff_finiteDimensional
import Theorems.Thm_FredholmBanach_isFredholm_add_compact
import Theorems.Thm_FredholmBanach_isCompactOperator_of_finiteDimensional_range
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.RCLike.Lemmas

open Topology

theorem solution {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (u : E →L[𝕜] F) :
    [u.IsFredholm ∧ FredholmBanach.index u = 0,
      ∃ e : E ≃L[𝕜] F, FiniteDimensional 𝕜 (u - (e : E →L[𝕜] F)).range,
      ∃ e : E ≃L[𝕜] F, IsCompactOperator (u - (e : E →L[𝕜] F))].TFAE := by
  tfae_have 1 → 2 := by
    rintro ⟨hu, h0⟩
    haveI : FiniteDimensional 𝕜 u.ker := hu.finite_ker
    haveI : FiniteDimensional 𝕜 (F ⧸ u.range) := hu.finite_coker
    obtain ⟨P, hP⟩ := hu.closedComplemented_ker
    obtain ⟨C, hC⟩ := Submodule.exists_isCompl u.range
    let q : (F ⧸ u.range) ≃ₗ[𝕜] C := Submodule.quotientEquivOfIsCompl u.range C hC
    haveI : FiniteDimensional 𝕜 C := q.finiteDimensional
    have hrank : Module.finrank 𝕜 u.ker = Module.finrank 𝕜 C := by
      rw [← q.finrank_eq]; unfold FredholmBanach.index at h0; omega
    let φ : u.ker ≃ₗ[𝕜] C := LinearEquiv.ofFinrankEq _ _ hrank
    let f : E →L[𝕜] F :=
      C.subtypeL.comp ((φ : u.ker →ₗ[𝕜] C).toContinuousLinearMap.comp P)
    have hf : ∀ x, f x = (φ (P x) : F) := fun x => rfl
    have hPk : ∀ k : u.ker, P (k : E) = k := hP
    have hinj : Function.Injective (u + f) := by
      refine (injective_iff_map_eq_zero (u + f)).2 fun x hx => ?_
      rw [ContinuousLinearMap.add_apply, hf] at hx
      have hux : u x = 0 := by
        have h1 : u x ∈ C := by
          rw [eq_neg_of_add_eq_zero_left hx]; exact C.neg_mem (φ (P x)).2
        exact (Submodule.disjoint_def.1 hC.disjoint) _ (LinearMap.mem_range_self _ x) h1
      rw [hux, zero_add] at hx
      have hPx : P x = 0 := by
        have : φ (P x) = 0 := Subtype.ext hx
        simpa using this
      have hxk : x ∈ u.ker := hux
      have := hPk ⟨x, hxk⟩
      rw [hPx] at this
      simpa using congrArg Subtype.val this.symm
    have hsurj : Function.Surjective (u + f) := by
      intro y
      have hy : y ∈ u.range ⊔ C := by rw [hC.sup_eq_top]; trivial
      obtain ⟨r, ⟨x, rfl⟩, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
      set k : u.ker := φ.symm ⟨c, hc⟩
      have hk0 : u (k : E) = 0 := k.2
      have hPx0 : u (P x : E) = 0 := (P x).2
      refine ⟨x - (P x : E) + (k : E), ?_⟩
      have hPx' : P (x - (P x : E) + (k : E)) = k := by
        rw [map_add, map_sub, hPk, hPk, sub_self, zero_add]
      rw [ContinuousLinearMap.add_apply, hf, hPx']
      simp [k, hk0, hPx0]
    let e : E ≃L[𝕜] F := ContinuousLinearEquiv.ofBijective (u + f)
      (LinearMap.ker_eq_bot.mpr hinj) (LinearMap.range_eq_top.mpr hsurj)
    refine ⟨e, ?_⟩
    have hle : (u - (e : E →L[𝕜] F)).range ≤ C := by
      rintro _ ⟨x, rfl⟩
      have : (u - (e : E →L[𝕜] F)) x = -(φ (P x) : F) := by
        change u x - (u + f) x = _
        rw [ContinuousLinearMap.add_apply, hf]; abel
      change (u - (e : E →L[𝕜] F)) x ∈ C
      rw [this]; exact C.neg_mem (φ (P x)).2
    exact Submodule.finiteDimensional_of_le hle
  tfae_have 2 → 3 := by
    rintro ⟨e, he⟩
    exact ⟨e, FredholmBanach.isCompactOperator_of_finiteDimensional_range _ he⟩
  tfae_have 3 → 1 := by
    rintro ⟨e, he⟩
    have hk : (e : E →L[𝕜] F).ker = ⊥ := LinearMap.ker_eq_bot.mpr e.injective
    have hr : (e : E →L[𝕜] F).range = ⊤ := LinearMap.range_eq_top.mpr e.surjective
    haveI hs : Subsingleton (F ⧸ (e : E →L[𝕜] F).range) := by
      refine ⟨fun a b => ?_⟩
      induction a using Submodule.Quotient.induction_on with | _ a => ?_
      induction b using Submodule.Quotient.induction_on with | _ b => ?_
      rw [Submodule.Quotient.eq, hr]; trivial
    have hq : Module.finrank 𝕜 (F ⧸ (e : E →L[𝕜] F).range) = 0 := Module.finrank_zero_of_subsingleton
    have he0 : (e : E →L[𝕜] F).IsFredholm := by
      refine (FredholmBanach.isFredholm_iff_finiteDimensional _).2 ⟨?_, ?_⟩
      · rw [hk]; infer_instance
      · infer_instance
    have hind : FredholmBanach.index (e : E →L[𝕜] F) = 0 := by
      unfold FredholmBanach.index
      rw [hq, hk, finrank_bot]; rfl
    have := FredholmBanach.isFredholm_add_compact he0 he
    rw [add_sub_cancel] at this
    exact ⟨this.1, this.2.trans hind⟩
  tfae_finish
