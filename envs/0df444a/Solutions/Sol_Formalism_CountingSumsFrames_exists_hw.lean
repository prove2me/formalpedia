-- Prove2me | solution 1 for Formalism.CountingSumsFrames.exists_hw
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:54:11.552679+00:00
-- url     : https://prove2.me/submissions/032f4e16-7f77-4bea-9be1-f90481e43d97

import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FockBlocks
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_RemoveS
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Theorems.Thm_Formalism_CountingSumsFrames_glAct_wtsp
import Theorems.Thm_Formalism_CountingSumsFrames_coeff_compP
import Theorems.Thm_Formalism_CountingSumsFrames_wcomp_mem
import Theorems.Thm_Formalism_CountingSumsFrames_multiDeg_finite

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.CountingSumsFrames
open Formalism.GM Formalism.GM.TM M MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}
namespace Formalism.CountingSumsFrames
theorem _root_.solution (LL : Letters N) (j : ℕ) (S : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]))
    (hSP : S ≤ Pol p r LL) (hS : ∀ c d, ∀ x ∈ S, glAct p LL j c d x ∈ S) (x : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (hx : x ∈ S) (hx0 : x ≠ 0) : ∃ h ∈ S, h ≠ 0 ∧ ∃ μ, h ∈ HWC p LL j univ μ := by
  classical
  let wv : (Fin N × Fin r →₀ ℕ) → (Fin r → ℤ) := fun m c => wt LL j c m
  let Wt : Set (Fin r → ℤ) := {μ | ∃ y ∈ S, y ≠ 0 ∧ y ∈ WtSpC p LL j univ μ}
  have hWfin : Wt.Finite := by
    refine ((multiDeg_finite (r := r) LL).image wv).subset ?_
    rintro μ ⟨y, hyS, hy0, hyW⟩
    obtain ⟨m, hm⟩ : ∃ m, m ∈ y.support := by
      by_contra hc; push Not at hc
      exact hy0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
    have hP := hSP hyS
    rw [Pol, mem_restrictSupport_iff] at hP
    rw [WtSpC, mem_restrictSupport_iff] at hyW
    refine ⟨m, hP (Finset.mem_coe.mpr hm), ?_⟩
    funext c
    exact hyW (Finset.mem_coe.mpr hm) c (Finset.mem_univ c)
  obtain ⟨m0, hm0⟩ : ∃ m, m ∈ x.support := by
    by_contra hc; push Not at hc
    exact hx0 (MvPolynomial.support_eq_empty.mp (Finset.eq_empty_of_forall_notMem hc))
  have hne : (hWfin.toFinset).Nonempty := by
    refine ⟨wv m0, hWfin.mem_toFinset.mpr ⟨_, wcomp_mem LL j S (fun c => hS c c) (wv m0) x hx, ?_, ?_⟩⟩
    · intro h0
      have := congrArg (coeff m0) h0
      rw [coeff_compP, if_pos (fun c => rfl), coeff_zero] at this
      exact (mem_support_iff.mp hm0) this
    · rw [WtSpC, mem_restrictSupport_iff]
      intro m hm c _
      rw [Finset.mem_coe, mem_support_iff, coeff_compP] at hm
      split_ifs at hm with h
      · exact h c
      · exact absurd rfl hm
  obtain ⟨μ, hμ, hmax⟩ := Finset.exists_max_image hWfin.toFinset (fun μ : Fin r → ℤ => -∑ c : Fin r, ((c : ℕ) : ℤ) * μ c) hne
  obtain ⟨y, hyS, hy0, hyW⟩ := hWfin.mem_toFinset.mp hμ
  refine ⟨y, hyS, hy0, μ, Submodule.mem_inf.mpr ⟨hyW, ?_⟩⟩
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  rintro c d ⟨_, _, hcd⟩
  by_contra hz
  have hmem : shiftW μ c d ∈ hWfin.toFinset :=
    hWfin.mem_toFinset.mpr ⟨_, hS c d y hyS, hz, glAct_wtsp LL j c d μ y hyW⟩
  have h1 := hmax _ hmem
  have h2 : (-∑ c' : Fin r, ((c' : ℕ) : ℤ) * shiftW μ c d c') = (-∑ c' : Fin r, ((c' : ℕ) : ℤ) * μ c') + (((d : ℕ) : ℤ) - ((c : ℕ) : ℤ)) := by
    simp only [shiftW, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  have h3 : ((c : ℕ) : ℤ) < ((d : ℕ) : ℤ) := by exact_mod_cast hcd
  linarith
end Formalism.CountingSumsFrames
