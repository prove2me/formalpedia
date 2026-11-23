-- Prove2me | solution 1 for Formalism.UG.P.levelaf_denom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:30.602152+00:00
-- url     : https://prove2.me/submissions/5b6a4060-4617-44fe-8b34-c0895188d21c

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Theorems.Thm_Formalism_UG_P_levelaf_adele_denom
import Theorems.Thm_Formalism_UG_P_levelaf_tmul_mem
import Theorems.Thm_Formalism_UG_P_levelafC_mem
import Theorems.Thm_Formalism_UG_P_levelafC_mul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.UG.P
theorem _root_.solution (x : 𝒜) : ∃ d : 𝓞 F, d ≠ 0 ∧ levelafC E d * x ∈ 𝒮 := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, by rw [mul_zero]; exact zero_mem _⟩
  | tmul e a =>
    have halg : Algebra.IsAlgebraic ℤ E :=
      (IsFractionRing.comap_isAlgebraic_iff (A := ℤ) (K := ℚ)).2 inferInstance
    obtain ⟨m, hm0, hm⟩ := (halg.1 e).exists_integral_multiple
    obtain ⟨d, hd0, hd⟩ := levelaf_adele_denom a
    refine ⟨(m : 𝓞 F) * d, mul_ne_zero (Int.cast_ne_zero.2 hm0) hd0, ?_⟩
    have e1 : levelafC E ((m : 𝓞 F) * d) * (e ⊗ₜ a) =
        algebraMap (𝓞 E) E ⟨m • e, hm⟩ ⊗ₜ[F] (algebraMap (𝓞 F) _ d * a) := by
      simp only [levelafC, Algebra.TensorProduct.tmul_mul_tmul, one_mul, map_mul, map_intCast]
      rw [show algebraMap (𝓞 E) E ⟨m • e, hm⟩ = m • e from rfl, TensorProduct.smul_tmul,
        zsmul_eq_mul, mul_assoc]
    rw [e1]; exact levelaf_tmul_mem _ hd
  | add x y hx hy =>
    obtain ⟨dx, hx0, hx⟩ := hx
    obtain ⟨dy, hy0, hy⟩ := hy
    refine ⟨dx * dy, mul_ne_zero hx0 hy0, ?_⟩
    have : levelafC E (dx * dy) * (x + y) =
        levelafC E dy * (levelafC E dx * x) + levelafC E dx * (levelafC E dy * y) := by
      rw [levelafC_mul]; ring
    rw [this]
    exact add_mem (mul_mem (levelafC_mem _) hx) (mul_mem (levelafC_mem _) hy)
end Formalism.UG.P
