-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.HighestWeightPolynomials.hw_cpol
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T17:49:54.675639+00:00
-- url     : https://prove2.me/submissions/3820c85f-113c-48b7-b8af-a2474738bc1d

import Definitions.Def_Formalism_HermitianCurvature_CapelliDeterminantAndBranching
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_QuantumMinorCommutation
import Definitions.Def_Lemmata_GeneralBFactSecondTerForm_Imports
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HighestWeightPolynomials
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx2_PolyFam_at
import Theorems.Thm_Formalism_FourierDecayAlt_Qr_mem_CapSp
import Theorems.Thm_Formalism_REAL_quantumDetHighestWeight_holds


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.HighestWeightPolynomials
open Formalism.REAL Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Qr
variable {V : Type} [AddCommGroup V] [Module ℂ V]
namespace Formalism.FourierDecayAlt.P.HighestWeightPolynomials
theorem _root_.solution {n : ℕ} {E : Fin n → Fin n → Module.End ℂ V} {m ν : Fin n → ℂ} {v : V} (hE : GlRel E)
    (hv : v ∈ CapSp E m) (hv0 : v ≠ 0) (hw : IsHW E ν v) (w : ℂ) :
    cpol m w = cpol (fun k => ν k - ((k : ℕ) : ℂ)) w := by
  have h1 := quantumDetHighestWeight_holds V n E ν v hE hw w
  rw [mem_CapSp.1 hv w] at h1
  have h2 := smul_left_injective ℂ hv0 h1
  rw [h2]
  unfold cpol
  refine Finset.prod_congr rfl fun k _ => ?_
  ring
end Formalism.FourierDecayAlt.P.HighestWeightPolynomials
