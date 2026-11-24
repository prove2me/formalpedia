-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.exists_hwC
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:55:29.986604+00:00
-- url     : https://prove2.me/submissions/71beed14-b201-4404-9e57-69552e0ded64

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_glAct_wtspC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wcomp_memC
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_compP
import Theorems.Thm_Formalism_CountingSumsFrames_multiDeg_finite
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_E_apply
import Theorems.Thm_Formalism_GM_QuotientRingDecomposition_divQ_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GM.QuotientRingDecomposition.E_apply
attribute [local simp] Formalism.GM.QuotientRingDecomposition.divQ_apply



set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters N) (j : ℕ) (Cs : Finset (Fin r))
    (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hSP : S ≤ Pol p r LL) (hS : ∀ c ∈ Cs, ∀ d ∈ Cs, ∀ x ∈ S, glAct p LL j c d x ∈ S)
    (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ S) (hx0 : x ≠ 0) : ∃ h ∈ S, h ≠ 0 ∧ ∃ μ, h ∈ HWC p LL j Cs μ := by
  classical
  have hSd : ∀ c ∈ Cs, ∀ z ∈ S, glAct p LL j c c z ∈ S := fun c hc z hz => hS c hc c hc z hz
  have hsupp : ∀ z ∈ S, ∀ m ∈ z.support, MultiDeg LL m := by
    intro z hz m hm
    have := hSP hz
    rw [Pol, mem_restrictSupport_iff] at this
    exact this (Finset.mem_coe.mpr hm)
  have hcong : ∀ (μ ν : Fin r → ℤ), (∀ c ∈ Cs, μ c = ν c) → ∀ z ∈ WtSpC p LL j Cs μ, z ∈ WtSpC p LL j Cs ν := by
    intro μ ν hμν z hz
    rw [WtSpC, mem_restrictSupport_iff] at hz ⊢
    intro m hm
    have := hz hm
    rw [Set.mem_setOf_eq] at this ⊢
    intro c hc
    rw [this c hc, hμν c hc]
  set M0 := (multiDeg_finite (r := r) LL).toFinset with hM0
  set A := M0.filter (fun m => ∃ h ∈ S, h ≠ 0 ∧ h ∈ WtSpC p LL j Cs (fun c => wt LL j c m)) with hA
  set φ : (Fin N × Fin r →₀ ℕ) → ℤ := fun m => ∑ c ∈ Cs, -((c : ℕ) : ℤ) * wt LL j c m with hφ
  have hAne : A.Nonempty := by
    have hne : x.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
      exact hx0
    obtain ⟨m0, hm0⟩ := hne
    refine ⟨m0, ?_⟩
    rw [hA, Finset.mem_filter, hM0, Set.Finite.mem_toFinset]
    refine ⟨hsupp x hx m0 hm0, compP (fun m => ∀ c ∈ Cs, wt LL j c m = wt LL j c m0) x,
      wcomp_memC LL j Cs S hSd _ x hx, ?_, ?_⟩
    · intro h0
      have := congrArg (coeff m0) h0
      rw [coeff_compP, if_pos (fun c _ => rfl), coeff_zero] at this
      exact (mem_support_iff.mp hm0) this
    · rw [WtSpC, mem_restrictSupport_iff]
      intro m hm
      have hc : coeff m (compP (fun m => ∀ c ∈ Cs, wt LL j c m = wt LL j c m0) x) ≠ 0 :=
        mem_support_iff.mp (Finset.mem_coe.mp hm)
      rw [coeff_compP] at hc
      split_ifs at hc with hP
      · exact hP
      · exact absurd rfl hc
  obtain ⟨ms, hms, hmax⟩ := Finset.exists_max_image A φ hAne
  rw [hA, Finset.mem_filter] at hms
  obtain ⟨_, h, hhS, hh0, hhW⟩ := hms
  refine ⟨h, hhS, hh0, fun c => wt LL j c ms, ?_⟩
  simp only [HWC, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  refine ⟨hhW, fun c d hcd => ?_⟩
  obtain ⟨hc, hd, hlt⟩ := hcd
  by_contra hy0
  set y := glAct p LL j c d h with hy
  have hyS : y ∈ S := hS c hc d hd h hhS
  have hyW := glAct_wtspC LL j Cs c d (fun c => wt LL j c ms) h hhW
  have hne : y.support.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty, Ne, support_eq_empty]
    exact hy0
  obtain ⟨m', hm'⟩ := hne
  have hw' : ∀ e ∈ Cs, wt LL j e m' = shiftW (fun c => wt LL j c ms) c d e := by
    have := hyW
    rw [WtSpC, mem_restrictSupport_iff] at this
    exact this (Finset.mem_coe.mpr hm')
  have hm'A : m' ∈ A := by
    rw [hA, Finset.mem_filter, hM0, Set.Finite.mem_toFinset]
    exact ⟨hsupp y hyS m' hm', y, hyS, hy0, hcong _ _ (fun e he => (hw' e he).symm) y hyW⟩
  have hle := hmax m' hm'A
  have hcalc : φ m' = φ ms + ((d : ℕ) : ℤ) - ((c : ℕ) : ℤ) := by
    rw [hφ]
    dsimp only
    rw [Finset.sum_congr rfl (fun e he => by rw [hw' e he]),
      show (∑ e ∈ Cs, -((e : ℕ) : ℤ) * shiftW (fun c => wt LL j c ms) c d e) =
        ∑ e ∈ Cs, ((-((e : ℕ) : ℤ) * wt LL j e ms + (if c = e then -((e : ℕ) : ℤ) else 0)) -
          (if d = e then -((e : ℕ) : ℤ) else 0)) from
        Finset.sum_congr rfl (fun e _ => by simp only [shiftW]; split_ifs <;> ring),
      Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.sum_ite_eq, if_pos hc, if_pos hd]
    ring
  have hlt' : (c : ℕ) < (d : ℕ) := hlt
  have : ((c : ℕ) : ℤ) < ((d : ℕ) : ℤ) := by exact_mod_cast hlt'
  linarith
end Formalism.InvariantFactorPaths.L4
