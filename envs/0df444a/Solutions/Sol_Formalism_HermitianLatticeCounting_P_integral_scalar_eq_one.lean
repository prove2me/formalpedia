-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.integral_scalar_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:11:04.433957+00:00
-- url     : https://prove2.me/submissions/d90ef16e-effa-411a-bfcf-9f63f266c316

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_isInt_add
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_isInt_map
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_isInt_mul
import Theorems.Thm_Formalism_HermitianLatticeCounting_P_IntegralityLocalGlobal_locGlob


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : SIntOne := by
  intro E _ _ σ T T' g s a c hT hT' hco hs1 hs2 ha hloc
  have hTE : (T : E) ≠ 0 := by exact_mod_cast hT.ne'
  have hTE' : (T' : E) ≠ 0 := by exact_mod_cast hT'.ne'
  have key : IsInt ((g : E) ^ 2 * s / ((T : E) * T')) := by
    apply locGlob
    intro P hP
    by_cases hg : (g : 𝓞 E) ∈ P
    · have hTT : ((T * T' : ℕ) : 𝓞 E) ∉ P := by
        intro h
        have hc : IsCoprime ((g : ℤ)) ((T * T' : ℕ) : ℤ) := Nat.isCoprime_iff_coprime.mpr hco
        obtain ⟨u, v, huv⟩ := hc
        have h1 : (1 : 𝓞 E) ∈ P := by
          have e : (1 : 𝓞 E) = (u : 𝓞 E) * (g : 𝓞 E) + (v : 𝓞 E) * ((T * T' : ℕ) : 𝓞 E) := by
            have := congrArg (Int.cast : ℤ → 𝓞 E) huv
            push_cast at this ⊢; exact this.symm
          rw [e]; exact P.add_mem (P.mul_mem_left _ hg) (P.mul_mem_left _ h)
        exact hP.ne_top ((Ideal.eq_top_iff_one P).mpr h1)
      refine ⟨((T * T' : ℕ) : 𝓞 E), hTT, ?_⟩
      have : (((T * T' : ℕ) : 𝓞 E) : E) * ((g : E) ^ 2 * s / ((T : E) * T')) =
          (g : E) * a * σ ((g : E) * a) - (g : E) ^ 2 := by
        rw [hs2]; push_cast; simp only [map_mul, map_natCast]; field_simp
      rw [this]
      have h3 := isInt_mul ha (isInt_map σ ha)
      have h4 : IsInt (-(g : E) ^ 2) := ⟨-(g : 𝓞 E) ^ 2, by simp⟩
      have h5 := isInt_add h3 h4
      simpa [sub_eq_add_neg] using h5
    · obtain ⟨y, z, hy, hyz⟩ := hloc P hP hg
      have hQ : (P.comap (RingOfIntegers.mapRingHom σ)).IsPrime := Ideal.comap_isPrime _ _
      obtain ⟨y', z', hy', hyz'⟩ := hloc _ hQ (by simpa [Ideal.mem_comap] using hg)
      refine ⟨y * RingOfIntegers.mapRingHom σ y', fun h => (hP.mem_or_mem h).elim hy hy', ?_⟩
      refine ⟨(g : 𝓞 E) ^ 2 * z * RingOfIntegers.mapRingHom σ z', ?_⟩
      have h2 : ((RingOfIntegers.mapRingHom σ y' : 𝓞 E) : E) * σ c =
          (T : E) * ((RingOfIntegers.mapRingHom σ z' : 𝓞 E) : E) := by
        have := congrArg σ hyz'
        simpa [RingOfIntegers.mapRingHom_apply] using this
      rw [hs1]
      have : ((y * RingOfIntegers.mapRingHom σ y' : 𝓞 E) : E) *
          ((g : E) ^ 2 * ((T' : E) * c * σ c / T) / ((T : E) * T')) =
          (g : E) ^ 2 * (((y : E) * c) * (((RingOfIntegers.mapRingHom σ y' : 𝓞 E) : E) * σ c)) /
            (T : E) ^ 2 := by
        push_cast; field_simp
      rw [this, hyz, h2]; push_cast; field_simp
  obtain ⟨β, hβ⟩ := key
  exact ⟨β, by rw [hβ]; field_simp⟩
end Formalism.HermitianLatticeCounting.P
