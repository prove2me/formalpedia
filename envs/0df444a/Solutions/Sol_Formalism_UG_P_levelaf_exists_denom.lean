-- Prove2me | solution 1 for Formalism.UG.P.levelaf_exists_denom
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:57:37.142522+00:00
-- url     : https://prove2.me/submissions/a7797fbf-f5f7-4671-afb9-7214471af8fe

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Theorems.Thm_Formalism_UG_P_levelafC_mem
import Theorems.Thm_Formalism_UG_P_levelafC_mul
import Theorems.Thm_Formalism_UG_P_levelaf_denom

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
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
namespace Formalism.UG.P
theorem _root_.solution (g : GL n 𝒜) : ∃ d : 𝓞 F, d ≠ 0 ∧ ∃ c : 𝒮, (c : 𝒜) = levelafC E d ∧
    (c : 𝒜) • (g : Matrix n n 𝒜) ∈ (RingHom.mapMatrix (m := n) (𝒮).subtype).range ∧
    (c : 𝒜) • ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) ∈ (RingHom.mapMatrix (m := n) (𝒮).subtype).range := by
  classical
  let f : (n × n) ⊕ (n × n) → 𝒜 := fun i => match i with
    | .inl p => (g : Matrix n n 𝒜) p.1 p.2
    | .inr p => ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) p.1 p.2
  choose d hd0 hd using fun i => levelaf_denom (E := E) (f i)
  have hmem : ∀ i, levelafC E (∏ k, d k) * f i ∈ 𝒮 := by
    intro i
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), levelafC_mul,
      mul_comm (levelafC E (d i)), mul_assoc]
    exact mul_mem (levelafC_mem _) (hd i)
  refine ⟨∏ k, d k, Finset.prod_ne_zero_iff.2 fun i _ => hd0 i, ⟨_, levelafC_mem _⟩, rfl, ?_, ?_⟩
  · refine ⟨Matrix.of fun i j => ⟨levelafC E (∏ k, d k) * (g : Matrix n n 𝒜) i j,
      hmem (.inl (i, j))⟩, ?_⟩
    ext i j; simp
  · refine ⟨Matrix.of fun i j => ⟨levelafC E (∏ k, d k) * ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) i j,
      hmem (.inr (i, j))⟩, ?_⟩
    ext i j; simp
end Formalism.UG.P
