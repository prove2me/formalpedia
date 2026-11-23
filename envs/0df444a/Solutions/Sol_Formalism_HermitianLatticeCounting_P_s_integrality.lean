-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.s_integrality
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:10:27.078218+00:00
-- url     : https://prove2.me/submissions/11a7162f-7752-4a46-877f-1508bbcd9bd5

import Definitions.Def_Formalism_FlagUnipotentLattices_DetIndexProductHyperbolicInequality
import Definitions.Def_Formalism_HyperbolicPlaceProducts_ArithmeticCountRevised
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_ComplexMultiplicationRoot
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_isInt_mul
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_isInt_coe
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_isInt_map
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_locGlob
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_divGlob
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure
namespace Formalism.HermitianLatticeCounting.P
namespace IntegralityLocalGlobal
variable {E : Type} [Field E] [NumberField E]
end IntegralityLocalGlobal
open IntegralityLocalGlobal
private theorem exists_not_mem_prime_mul_eq_of_locIn {E : Type} [Field E] [NumberField E] (σ : E →+* E) (M M' g : ℕ) (u e : E)
    (hM : 0 < M) (he : e = (g : E) ^ 2 * ((M' : E) * u * σ u / (M : E)))
    (hu : ∀ P : Ideal (𝓞 E), P.IsPrime → (M : 𝓞 E) ∈ P → LocIn P u M)
    (P : Ideal (𝓞 E)) (hP : P.IsPrime) (hMP : (M : 𝓞 E) ∈ P) :
    ∃ y z : 𝓞 E, y ∉ P ∧ (y : E) * e = (M : E) * (M' : E) * (g : E) ^ 2 * (z : E) := by
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  let f : 𝓞 E →+* 𝓞 E := NumberField.RingOfIntegers.mapRingHom σ
  have hf : ∀ y : 𝓞 E, ((f y : 𝓞 E) : E) = σ (y : E) := fun y => rfl
  have hQ : (P.comap f).IsPrime := by
    haveI := hP
    first
    | exact Ideal.comap_isPrime f P
    | exact Ideal.IsPrime.comap f
    | infer_instance
  have hMQ : (M : 𝓞 E) ∈ P.comap f := by
    rw [Ideal.mem_comap, map_natCast]; exact hMP
  obtain ⟨y1, z1, hy1, h1⟩ := hu P hP hMP
  obtain ⟨y2, z2, hy2, h2⟩ := hu _ hQ hMQ
  have h2' : ((f y2 : 𝓞 E) : E) * σ u = (M : E) * ((f z2 : 𝓞 E) : E) := by
    have h3 := congrArg σ h2
    rw [map_mul, map_mul, map_natCast] at h3
    rw [hf, hf]; exact h3
  have hE : e * (M : E) = (g : E) ^ 2 * ((M' : E) * u * σ u) := by
    rw [he]
    first
    | rw [mul_div_assoc', div_mul_cancel₀ _ hM0]
    | field_simp
  have c1 : ((y1 * f y2 : 𝓞 E) : E) = (y1 : E) * ((f y2 : 𝓞 E) : E) := by
    first | rfl | (push_cast; rfl) | simp
  have c2 : ((z1 * f z2 : 𝓞 E) : E) = (z1 : E) * ((f z2 : 𝓞 E) : E) := by
    first | rfl | (push_cast; rfl) | simp
  refine ⟨y1 * f y2, z1 * f z2, ?_, ?_⟩
  · intro hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact hy1 h
    · exact hy2 (Ideal.mem_comap.mpr h)
  · rw [c1, c2]
    apply mul_right_cancel₀ hM0
    linear_combination ((y1 : E) * ((f y2 : 𝓞 E) : E)) * hE
      + ((g : E) ^ 2 * (M' : E) * (((f y2 : 𝓞 E) : E) * σ u)) * h1
      + ((g : E) ^ 2 * (M' : E) * (M : E) * (z1 : E)) * h2'
namespace IntegralityLocalGlobal
end IntegralityLocalGlobal
end Formalism.HermitianLatticeCounting.P
end

set_option autoImplicit false
open Module NumberField Formalism.HermitianLatticeCounting.LocalIntegralStructure
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open IntegralityLocalGlobal
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : Formalism.HermitianLatticeCounting.LocalIntegralStructure.SInt := by
  intro E _ _ σ T T' g s b c hT hT' hs1 hs2 hgb hgc hc hb
  have hT0 : (T : E) ≠ 0 := Nat.cast_ne_zero.mpr hT.ne'
  have hTT : 0 < T * T' := Nat.mul_pos hT hT'
  have e1 : (g : E) ^ 2 * s = (g : E) ^ 2 * ((T' : E) * c * σ c / (T : E)) := by rw [hs1]
  have e2 : (g : E) ^ 2 * s = (g : E) ^ 2 * ((T : E) * b * σ b / (T' : E)) := by rw [hs2]
  have hint : IsInt ((g : E) ^ 2 * s) := by
    apply locGlob
    intro P hP
    by_cases hTP : (T : 𝓞 E) ∈ P
    · obtain ⟨y, z, hy, hyz⟩ := exists_not_mem_prime_mul_eq_of_locIn σ T T' g c _ hT e1 hc P hP hTP
      refine ⟨y, hy, ?_⟩
      rw [hyz]
      convert isInt_coe ((T : 𝓞 E) * (T' : 𝓞 E) * (g : 𝓞 E) ^ 2 * z) using 1
      push_cast; ring
    · refine ⟨(T : 𝓞 E), hTP, ?_⟩
      have hh := isInt_mul (isInt_mul (isInt_coe (T' : 𝓞 E)) hgc) (isInt_map σ hgc)
      convert hh using 1
      rw [hs1, map_mul, map_natCast]
      push_cast
      first
      | (rw [mul_div_assoc', mul_div_assoc', mul_div_cancel_left₀ _ hT0]; ring)
      | (field_simp; ring)
      | field_simp
  have hloc : ∀ P : Ideal (𝓞 E), P.IsPrime → ((T * T' : ℕ) : 𝓞 E) ∈ P →
      LocIn P ((g : E) ^ 2 * s) (T * T') := by
    intro P hP hmem
    rw [Nat.cast_mul] at hmem
    unfold LocIn
    rcases hP.mem_or_mem hmem with h | h
    · obtain ⟨y, z, hy, hyz⟩ := exists_not_mem_prime_mul_eq_of_locIn σ T T' g c _ hT e1 hc P hP h
      refine ⟨y, (g : 𝓞 E) ^ 2 * z, hy, ?_⟩
      rw [hyz]; push_cast; ring
    · obtain ⟨y, z, hy, hyz⟩ := exists_not_mem_prime_mul_eq_of_locIn σ T' T g b _ hT' e2 hb P hP h
      refine ⟨y, (g : 𝓞 E) ^ 2 * z, hy, ?_⟩
      rw [hyz]; push_cast; ring
  obtain ⟨β, hβ⟩ := divGlob _ (T * T') hTT hint hloc
  refine ⟨β, ?_⟩
  rw [hβ]; push_cast; ring
end Formalism.HermitianLatticeCounting.P
