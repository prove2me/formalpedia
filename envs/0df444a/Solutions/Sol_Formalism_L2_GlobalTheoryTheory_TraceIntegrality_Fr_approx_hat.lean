-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr.approx_hat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:14:02.69129+00:00
-- url     : https://prove2.me/submissions/b15c92eb-668e-4b50-accf-5156c9dca21d

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_RationalPointsLeHolds
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL4_PFrCore
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_vi_mem_hat
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_natCast_ne
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_TraceIntegrality_Fr_levelafC_nat
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
import Theorems.Thm_Formalism_UG_P_csGlob_approx
import Theorems.Thm_Formalism_UG_P_csGlob_intAdApprox
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.TraceIntegrality Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions Formalism.L2.GlobalTheoryTheory.Comp
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
theorem _root_.solution (M : ℕ) (hM : M ≠ 0) (Λ : Submodule (𝓞 E) (n → E)) (u : n → 𝒜)
    (hu : u ∈ hat F Λ) : ∃ x ∈ Λ, ∃ z ∈ hat F Λ, u = vi F x + (M : 𝒜) • z := by
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨x, hx, rfl⟩ := hu
    exact ⟨x, hx, 0, zero_mem _, by rw [smul_zero, add_zero]; rfl⟩
  | zero => exact ⟨0, zero_mem _, 0, zero_mem _, by funext i; simp [vi]⟩
  | add u w _ _ hu hw =>
    obtain ⟨x, hx, z, hz, rfl⟩ := hu
    obtain ⟨x', hx', z', hz', rfl⟩ := hw
    refine ⟨x + x', add_mem hx hx', z + z', add_mem hz hz', ?_⟩
    funext i
    simp only [vi, Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add]
    ring
  | smul s u _ hu =>
    obtain ⟨x, hx, z, hz, rfl⟩ := hu
    obtain ⟨b, t, ht, hs⟩ := csGlob_approx (F := F) (E := E) csGlob_intAdApprox ((M : ℕ) : 𝓞 F)
      (natCast_ne M hM) (s : 𝒜) s.2
    refine ⟨b • x, Submodule.smul_mem _ b hx,
      (⟨t, ht⟩ : 𝒮) • vi F x + s • z, add_mem (Submodule.smul_mem _ _ (vi_mem_hat hx)) (Submodule.smul_mem _ _ hz), ?_⟩
    rw [levelafC_nat] at hs
    funext i
    have e1 : vi F (b • x) i = ιA (algebraMap (𝓞 E) E b) * ιA (x i) := by simp [vi, Algebra.smul_def, map_mul]
    rw [Pi.add_apply, e1]
    show (s : 𝒜) * (vi F x i + (M : 𝒜) * z i) = _ + (M : 𝒜) * (t * vi F x i + (s : 𝒜) * z i)
    rw [hs]
    simp only [vi]
    ring
end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.Fr
