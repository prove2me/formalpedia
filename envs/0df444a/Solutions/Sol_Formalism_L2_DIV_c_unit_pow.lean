-- Prove2me | solution 1 for Formalism.L2.DIV.c_unit_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T13:25:25.443859+00:00
-- url     : https://prove2.me/submissions/52cae99a-c6fe-4a7d-9a9e-c3594fc803df

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Afsplit
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_DivisibilityProofs_TuplesP
import Theorems.Thm_Formalism_UG_P_levelaf_finite_quot


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling Formalism.UG.P
open scoped nonZeroDivisors
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
local notation "ιE" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)
namespace Formalism.L2.DIV
theorem _root_.solution (N : ℕ) (hN : 0 < N) : ∃ m : ℕ, 0 < m ∧ ∀ u ∈ intU F E, u ^ m ∈ congN F E N := by
  have hfin : Finite (RInt F E ⧸ Ideal.span {(N : RInt F E)}) := by
    apply levelaf_finite_quot (N : 𝓞 F) (by exact_mod_cast hN.ne')
    rw [levelafC, map_natCast]
    show ((N : RInt F E) : AfE F E) =
      (Algebra.TensorProduct.includeRight : FiniteAdeleRing (𝓞 F) F →ₐ[F] AfE F E) (N : FiniteAdeleRing (𝓞 F) F)
    rw [map_natCast]
    simp
  refine ⟨Nat.card (RInt F E ⧸ Ideal.span {(N : RInt F E)})ˣ, Nat.card_pos, ?_⟩
  intro u hu
  rw [intU, Submonoid.mem_units_iff] at hu
  let u' : (RInt F E)ˣ := ⟨⟨u, hu.1⟩, ⟨((u⁻¹ : (AfE F E)ˣ) : AfE F E), hu.2⟩,
    Subtype.ext u.mul_inv, Subtype.ext u.inv_mul⟩
  refine ⟨u' ^ Nat.card (RInt F E ⧸ Ideal.span {(N : RInt F E)})ˣ, ?_, ?_⟩
  · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_pow, pow_card_eq_one']
  · rw [map_pow]
    congr 1
end Formalism.L2.DIV
