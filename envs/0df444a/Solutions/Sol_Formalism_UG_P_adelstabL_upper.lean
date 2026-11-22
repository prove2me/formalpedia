-- Prove2me | solution 1 for Formalism.UG.P.adelstabL_upper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T19:50:51.585838+00:00
-- url     : https://prove2.me/submissions/535eca9e-cb4e-4b95-b82e-a4f0149868e5

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Adelstab
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Theorems.Thm_Formalism_UG_P_adelstabL_den
import Theorems.Thm_Formalism_UG_P_adelstabL_incl_int
import Theorems.Thm_Formalism_UG_P_adelstab_incl_C


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.UG.P
theorem _root_.solution (Λ : Submodule (𝓞 E) (n → E)) (hfin : Module.Finite (𝓞 E) Λ) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ v ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ, ∀ i,
      levelafC E c * v i ∈ 𝒮 := by
  classical
  obtain ⟨s, hs⟩ : Λ.FG := Module.Finite.iff_fg.mp hfin
  obtain ⟨m, hm0, hm⟩ := adelstabL_den (fun p : s × n => (p.1 : n → E) p.2)
  have hΛ : ∀ x ∈ Λ, ∀ k, IsIntegral ℤ ((m : E) * x k) := by
    intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => intro k; exact hm (⟨x, hx⟩, k)
    | zero => intro k; simp [isIntegral_zero]
    | add x y _ _ hx hy => intro k; simpa [mul_add] using (hx k).add (hy k)
    | smul r x _ hx =>
      intro k
      have : (m : E) * (r • x) k = algebraMap (𝓞 E) E r * ((m : E) * x k) := by
        simp [Algebra.smul_def]; ring
      rw [this]
      exact (RingOfIntegers.isIntegral_coe r).mul (hx k)
  refine ⟨(m : 𝓞 F), Int.cast_ne_zero.2 hm0, fun v hv => ?_⟩
  have hC : levelafC E (m : 𝓞 F) = ι (m : E) := by
    rw [← adelstab_incl_C, map_intCast]
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨x, hx, rfl⟩ := hv
    intro i
    rw [hC, ← map_mul]
    exact adelstabL_incl_int _ (hΛ x hx i)
  | zero => intro i; simp
  | add v w _ _ hv hw => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (hv i) (hw i)
  | smul s v _ hv =>
    intro i
    rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem s.2 (hv i)
end Formalism.UG.P
