-- Prove2me | solution 1 for Formalism.L2.SG.Pf.RedBasicsPf.coords
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:09:05.636955+00:00
-- url     : https://prove2.me/submissions/5b827866-ed0d-4590-b2a0-269c6ef54661

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RowDictCore
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicClassFiniteness_DictAll
import Definitions.Def_Formalism_LocalToGlobal_SiegelLatticeTheory_FlagStabilizerTensors_RootLatticeThresholds_RedBasicsPf
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_iv_mem_w
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_dense
import Theorems.Thm_Formalism_L2_SG_Pf_RedBasicsPf_iv_lin

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
theorem _root_.solution {p : ℕ} (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {m : ℕ}
    {b : Fin m → (Fin I.n → I.E)} (hb : IsRedBasis0 I w b) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    ∃ c : Fin m → ℤ, y - ∑ j, (c j : I.E ⊗[I.F] Af I.F) • iv I (b j) ∈ lamAf (F := I.F) (wLat0 I w) := by
  obtain ⟨l, hl, hyl⟩ := dense I w hp hcard hy
  obtain ⟨c, hc⟩ := hb.2 l hl
  refine ⟨c, ?_⟩
  have h2 := iv_mem_w I w hc
  rw [iv_lin] at h2
  have h3 := Submodule.add_mem _ hyl h2
  rwa [sub_add_sub_cancel] at h3
end Formalism.L2.SG.Pf.RedBasicsPf
