-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.L4.resMMZL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:48:59.431398+00:00
-- url     : https://prove2.me/submissions/9f464fa7-2109-4d59-8437-7fa9716a244d

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementG
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_StatementF
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_MulEarlyModP
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_DischargeHeightBound
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_FinalM
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_GramBoundUnconditionalOfSat
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eproj_Y
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eproj_fix
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_eproj_res
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_hypE_eproj
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtComp_Y
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtComp_fix
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtComp_int
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtComp_mem
import Theorems.Thm_Formalism_InvariantFactorPaths_L4_wtComp_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames Formalism.InvariantFactorPaths.PW MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {K r : ℕ} [NeZero r]
namespace Formalism.InvariantFactorPaths.L4
theorem _root_.solution (LL : Letters (K + 1)) {q : ℕ} (J : Fin q → ℕ) (M : Fin q → WithTop ℤ) (ρ : Fin r)
    (w : Fin r → ℤ) (e1 c0 : ℕ) (hHP : HypP p LL ρ e1) (hHE : HypE p LL ρ e1) (hSat : ResSatL p LL J M ρ c0)
    (x : MvPolynomial (Fin (K + 1) × Fin r) ℚ_[p]) (hx : x ∈ XH p LL J M ρ w)
    (hxI : x ∈ IntPol p (Fin (K + 1) × Fin r)) :
    ∃ h ∈ MMwZ p LL J M ρ w, initPart (Fin.last K, ρ) 0 h = ((p : ℚ_[p]) ^ (e1 + c0)) • x := by
  obtain ⟨hx1, hxW⟩ := Submodule.mem_inf.mp hx
  obtain ⟨hxX, hxH⟩ := Submodule.mem_inf.mp hx1
  obtain ⟨h0, hh0, hh0I, hres⟩ := hSat x hxX hxI
  obtain ⟨PE, hPE, -, hInt⟩ := hypE_eproj LL ρ e1 hHE (K + 1) le_rfl w
  have hY := wtComp_Y LL J M w h0 hh0
  have hW := wtComp_mem (p := p) LL (K + 1) w h0
  refine ⟨((p : ℚ_[p]) ^ e1) • PE (wtComp p LL (K + 1) w h0), Submodule.mem_inf.mpr
    ⟨Submodule.smul_mem (MMw p LL J M ρ w) _ (eproj_Y LL J M ρ w e1 hHP PE hPE _ hY hW),
      hInt _ (Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hY).1, wtComp_int LL (K + 1) w h0 hh0I⟩) hW⟩, ?_⟩
  change resL p (Fin.last K, ρ) 0 (((p : ℚ_[p]) ^ e1) • PE (wtComp p LL (K + 1) w h0)) = _
  change resL p (Fin.last K, ρ) 0 h0 = _ at hres
  rw [map_smul, ← eproj_res LL (K + 1) ρ w PE hPE (Fin.last K) 0 _ hW, wtComp_res, hres,
    wtComp_fix LL (K + 1) w _ (Submodule.smul_mem _ _ hxW), map_smul,
    eproj_fix LL (K + 1) ρ w PE hPE x (Submodule.mem_inf.mpr ⟨hxH, hxW⟩), smul_smul, ← pow_add]
end Formalism.InvariantFactorPaths.L4
