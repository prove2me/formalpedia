-- Prove2me | solution 1 for Formalism.QuantumDeterminants.capelli_highest_weight_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:59:19.992696+00:00
-- url     : https://prove2.me/submissions/b3bcb935-55cb-4d66-b858-cc74dbc55563

import Definitions.Def_Formalism_FormalDegreeBessel_StatementIO
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_FinalF
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_IOCentral
import Theorems.Thm_Formalism_QuantumDeterminants_ioE_rep
import Theorems.Thm_Formalism_QuantumDeterminants_io_rep_mk
import Theorems.Thm_Formalism_QuantumDeterminants_io_qminor_rep
import Theorems.Thm_Formalism_QuantumDeterminants_io_gl
import Theorems.Thm_Formalism_REAL_qDetHW


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ContDiff
noncomputable section
open Formalism Formalism.QuantumDeterminants
open Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
namespace Formalism.QuantumDeterminants
theorem _root_.solution : CapHW := by
  intro n ε E _ _ f ν hf hHW g hg
  obtain ⟨x, hx⟩ := io_rep_mk (ε := ε) (E := E) hf
  have hW : IsHW (ioE ε E) ν x := by
    refine ⟨fun a => ?_, fun a b hab => ?_⟩
    · refine Subtype.ext (funext fun p => ?_)
      obtain ⟨g', hg'⟩ := p
      calc (ioE ε E a a x : IOPt ε → E) ⟨g', hg'⟩ = EabV ε a a f g' := (ioE_rep hx a a g' hg').symm
        _ = ν a • f g' := (hHW g' hg').1 a
        _ = ν a • (x : IOPt ε → E) ⟨g', hg'⟩ := by rw [hx g' hg']
        _ = ((ν a • x : ioS ε E) : IOPt ε → E) ⟨g', hg'⟩ := rfl
    · refine Subtype.ext (funext fun p => ?_)
      obtain ⟨g', hg'⟩ := p
      calc (ioE ε E a b x : IOPt ε → E) ⟨g', hg'⟩ = EabV ε a b f g' := (ioE_rep hx a b g' hg').symm
        _ = 0 := (hHW g' hg').2 a b hab
        _ = ((0 : ioS ε E) : IOPt ε → E) ⟨g', hg'⟩ := rfl
  have hu : ∀ u : ℂ, capelli ε u f g = (∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • f g := by
    intro u
    calc capelli ε u f g = (qminor (ioE ε E) id id u x : IOPt ε → E) ⟨g, hg⟩ :=
          io_qminor_rep id id u hx g hg
      _ = (((∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • x : ioS ε E) : IOPt ε → E) ⟨g, hg⟩ :=
          congrArg (fun y : ioS ε E => (y : IOPt ε → E) ⟨g, hg⟩)
            (qDetHW (ioS ε E) n (ioE ε E) ν x (io_gl ε E) hW u)
      _ = (∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • (x : IOPt ε → E) ⟨g, hg⟩ := rfl
      _ = (∏ k : Fin n, (u - ((k : ℕ) : ℂ) + ν k)) • f g := by rw [hx g hg]
  refine ⟨hu, fun Y => ?_⟩
  rw [hu]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by ring
end Formalism.QuantumDeterminants
