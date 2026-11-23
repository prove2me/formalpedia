-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.ycond_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:40.182846+00:00
-- url     : https://prove2.me/submissions/f80d47bf-6db0-4e41-991a-4dcead204313

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_FirstWeightLeOfSupport
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_ResInto
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_keep_wt
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_glAct
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_le_ycond

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
section Res
variable {p : ℕ} [Fact p.Prime] {σ : Type}
end Res
section Last
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
private theorem yCond_le_restrictSupport_wt_le {N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ) :
    YCond p LL j Mt ≤
      restrictSupport ℚ_[p] {m : Fin N × Fin r →₀ ℕ | ((wt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} :=
  sSup_le fun _ hS => hS.1
private theorem glAct_mem_yCond_of_neZero {N : ℕ} [NeZero r] (LL : Letters N) (j : ℕ) (Mt : WithTop ℤ)
    (a b : Fin r) : ∀ y ∈ YCond p LL j Mt, glAct p LL j a b y ∈ YCond p LL j Mt := by
  have h : YCond p LL j Mt ≤ (YCond p LL j Mt).comap (glAct p LL j a b) :=
    sSup_le fun _ hS y hy => le_sSup hS (hS.2 a b y hy)
  exact fun y hy => h hy
end Last
end Formalism.InvariantFactorPaths.L4
end

set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Mt : WithTop ℤ)
    (c : Fin r) : ∀ x ∈ YCond p LL (K + 1) Mt, pderiv (Fin.last K, c) x ∈ YCond p LL (K + 1) Mt := by
  intro x hx
  let G : Set (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
    {y | ∃ c' : Fin r, ∃ z ∈ YCond p LL (K + 1) Mt, y = pderiv (Fin.last K, c') z}
  have hSle : Submodule.span ℚ_[p] G ≤ restrictSupport ℚ_[p]
      {m : Fin (K + 1) × Fin r →₀ ℕ | ((wt LL (K + 1) 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    rw [Submodule.span_le]
    rintro y ⟨c', z, hz, rfl⟩
    exact pderiv_keep_wt LL hv c' Mt z (yCond_le_restrictSupport_wt_le LL (K + 1) Mt hz)
  have hSst : GlStable p LL (K + 1) (Submodule.span ℚ_[p] G) := by
    intro a b y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c', z, hz, rfl⟩ := hy
      have e := pderiv_glAct LL hv a b c' z
      rw [eq_sub_of_add_eq e.symm]
      refine Submodule.sub_mem _
        (Submodule.subset_span ⟨c', _, glAct_mem_yCond_of_neZero LL (K + 1) Mt a b z hz, rfl⟩) ?_
      split_ifs
      · exact Submodule.subset_span ⟨b, z, hz, rfl⟩
      · exact Submodule.zero_mem _
    | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
    | add y1 y2 _ _ h1 h2 =>
      rw [map_add]
      exact Submodule.add_mem _ h1 h2
    | smul t y _ h =>
      rw [map_smul]
      exact Submodule.smul_mem _ t h
  exact le_ycond LL (K + 1) Mt _ hSle hSst (Submodule.subset_span ⟨c, x, hx, rfl⟩)
end Formalism.InvariantFactorPaths.L4
