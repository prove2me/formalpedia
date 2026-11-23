-- Prove2me | solution 1 for Formalism.L2.Th1.E.Tor.restrict
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:33:31.040801+00:00
-- url     : https://prove2.me/submissions/8da93784-d0a2-4a70-b391-41a73c639625

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_StatementA
import Definitions.Def_Formalism_EllipticTorsion_FormalGroupPointsNoTorsion
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_FlowTwoTorsionWp
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_FrobeniusFibreCurves_LogarithmicSubstitution_LogSigmaOnePullbackSpec
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Series
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_TorsionTranslationPowers_NonsingularJetNorms_Taylor0ConstMul
import Theorems.Thm_Formalism_L2_Th1_E_Tor_int_mul_mem
import Theorems.Thm_Formalism_L2_Th1_B_Ph_hs


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PowerSeries
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.E
open Formalism.L2.Th1.F (opU sgStar th0 taylor0)
open Formalism.L2.Th1.B (fExp fLog)
open Formalism.L2.Th1.E.Tor
variable (l : ℕ) [Fact l.Prime] (L : PeriodPair) (ι : ℂ ≃+* ℂ_[l])
open Classical
namespace Formalism.L2.Th1.E.Tor
theorem _root_.solution (hS : AnalyticSys) (hA : PtOfAdd) (hZ : PtOfZero) (hI : PtOfInt)
    (hW : IntCurve (curveL l L ι)) (t : ℂ) (N : ℕ) (hN : 0 < N) (hlN : ¬ l ∣ N)
    (hNt : (N : ℂ) * t ∈ L.lattice) :
    IntPts (curveL l L ι) ((piOf l L ι hA).comp (AddSubgroup.zmultiples t).subtype) ∧
    IsTransSys (curveL l L ι) ((piOf l L ι hA).comp (AddSubgroup.zmultiples t).subtype)
      (fun s : AddSubgroup.zmultiples t => gT l L ι (s : ℂ)) := by
  constructor
  · rintro ⟨s, hs⟩ h0
    obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hs
    refine hI l L ι hW _ N hN hlN ?_ (fun hmem => h0 ((hZ l L ι _).2 hmem))
    have e : (N : ℂ) * (k • t) = (k : ℂ) * ((N : ℂ) * t) := by
      rw [zsmul_eq_mul]
      ring
    change (N : ℂ) * (k • t) ∈ L.lattice
    rw [e]
    exact int_mul_mem L k hNt
  · obtain ⟨h1, h2, h3⟩ := hS l L ι (piOf l L ι hA) (fun _ => rfl)
    exact ⟨fun s => h1 s, fun s => h2 s, fun P Q => h3 P Q⟩
end Formalism.L2.Th1.E.Tor
