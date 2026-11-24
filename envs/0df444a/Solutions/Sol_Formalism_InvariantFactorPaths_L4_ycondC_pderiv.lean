-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.ycondC_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:49:33.351824+00:00
-- url     : https://prove2.me/submissions/6e49aaeb-a44d-4f57-a693-6c7b35d1a78f

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementD
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_RaisingKeepsEarlyLetters
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_TypesLELeYcondC
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_DerivativeKeepsSpaceHolds
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_le_ycondC
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_glAct
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_pderiv_keep_wt
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_glStable
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_ycondC_le_supp


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ}
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution [NeZero r] (LL : Letters (K + 1)) (hv : LL.vec (Fin.last K) = true) (Cs : Finset (Fin r))
    (Mt : WithTop ℤ) (c : Fin r) (hc : c ∈ Cs) :
    ∀ x ∈ YCondC p LL (K + 1) Cs Mt, pderiv (Fin.last K, c) x ∈ YCondC p LL (K + 1) Cs Mt := by
  set B : Submodule ℚ_[p] (MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) :=
    ⨆ (c : Fin r) (_ : c ∈ Cs), (YCondC p LL (K + 1) Cs Mt).map (pderiv (Fin.last K, c)).toLinearMap with hB
  have hmem : ∀ c ∈ Cs, ∀ x ∈ YCondC p LL (K + 1) Cs Mt, pderiv (Fin.last K, c) x ∈ B := fun c hc x hx =>
    Submodule.mem_iSup_of_mem c (Submodule.mem_iSup_of_mem hc
      (Submodule.mem_map_of_mem (f := (pderiv (Fin.last K, c)).toLinearMap) hx))
  have hle : B ≤ YCondC p LL (K + 1) Cs Mt := by
    refine le_ycondC LL (K + 1) Cs Mt _ ?_ ?_
    · refine iSup_le fun c => iSup_le fun _ => Submodule.map_le_iff_le_comap.mpr fun x hx =>
        pderiv_keep_wt LL hv c Mt x (ycondC_le_supp LL (K + 1) Cs Mt hx)
    · intro a ha b hb
      have : B ≤ B.comap (glAct p LL (K + 1) a b) := by
        refine iSup_le fun c => iSup_le fun hc => ?_
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
        show glAct p LL (K + 1) a b (pderiv (Fin.last K, c) x) ∈ B
        have e : glAct p LL (K + 1) a b (pderiv (Fin.last K, c) x) =
            pderiv (Fin.last K, c) (glAct p LL (K + 1) a b x) - (if a = c then pderiv (Fin.last K, b) x else 0) := by
          rw [pderiv_glAct LL hv]; abel
        rw [e]
        refine Submodule.sub_mem _ (hmem c hc _ (ycondC_glStable LL (K + 1) Cs Mt a ha b hb x hx)) ?_
        split_ifs
        · exact hmem b hb x hx
        · exact Submodule.zero_mem _
      exact fun y hy => this hy
  intro x hx
  exact hle (hmem c hc x hx)
end Formalism.InvariantFactorPaths.L4
