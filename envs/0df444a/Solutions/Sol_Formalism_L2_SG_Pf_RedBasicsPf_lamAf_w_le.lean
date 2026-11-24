-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.lamAf_w_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:31:08.763266+00:00
-- url     : https://prove2.me/submissions/c4065696-1883-4ab7-81b1-8b5034516aa4

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open scoped TensorProduct Matrix Pointwise
open Formalism Formalism.L2 Formalism.L2.SG Formalism.L2.SG.Pf Formalism.L2.SG.Pf.RedBasicsPf
open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin
attribute [local instance] Ideal.Quotient.field
variable (I : AutInst) (w : HeightOneSpectrum (𝓞 I.E))
namespace Formalism.L2.SG.Pf.RedBasicsPf
theorem _root_.solution (S : Submodule (IntAf I.F I.E) (Fin I.n → I.E ⊗[I.F] Af I.F))
    (h : ∀ a ∈ w.asIdeal, ∀ y ∈ I.L, iv I (((a : 𝓞 I.E) : I.E) • y) ∈ S) :
    lamAf (F := I.F) (wLat0 I w) ≤ S := by
  show Submodule.span _ _ ≤ S
  rw [Submodule.span_le]
  rintro _ ⟨⟨v, hv⟩, rfl⟩
  show iv I v ∈ S
  rw [wLat0] at hv
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hx
    exact h a ha y hy
  | zero => rw [DictLat.iv_zero]; exact S.zero_mem
  | add x y _ _ hx hy => rw [DictLat.iv_add]; exact S.add_mem hx hy
  | smul a x _ hx =>
    rw [DictLat.iv_smulO]
    exact S.smul_mem (⟨Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E), DictLat.inclE_int I ⟨a, rfl⟩⟩ : IntAf I.F I.E) hx
end Formalism.L2.SG.Pf.RedBasicsPf
