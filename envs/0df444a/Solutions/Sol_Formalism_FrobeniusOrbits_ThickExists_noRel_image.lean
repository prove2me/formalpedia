-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.ThickExists.noRel_image
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:11:55.192801+00:00
-- url     : https://prove2.me/submissions/81e4ee89-ce12-469f-a4bb-59ebc8a55020

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Lemmata_GeneralBFactSecondLast_Imports
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickExists_coeff_zero
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickExists_sphere_rel
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickExists_cast_map
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Finset
noncomputable section
namespace Formalism.FrobeniusOrbits.ThickExists
private lemma sphere_mem_lemma {S d k : ℕ} {v : Fin S → ℕ} (hv : v ∈ Behrend.sphere S d k) :
    (∀ i, v i < d) ∧ ∑ i, v i ^ 2 = k := by
  simp only [Behrend.sphere, Finset.mem_filter, Behrend.mem_box] at hv
  exact hv
end Formalism.FrobeniusOrbits.ThickExists
namespace Formalism.FrobeniusOrbits
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.ThickExists
namespace Formalism.FrobeniusOrbits.ThickExists
theorem _root_.solution (L S d k : ℕ) (hL : 1 ≤ L) :
    NoRel ((Behrend.sphere S d k).image (Behrend.map (4 * L * d))) L := by
  unfold NoRel
  intro s₁ hs₁ s₂ hs₂ s₃ hs₃ h12 h13 h23 i j hi0 hiL hj0 hjL hij heq
  rw [Finset.mem_image] at hs₁ hs₂ hs₃
  obtain ⟨v₁, hv₁, rfl⟩ := hs₁
  obtain ⟨v₂, hv₂, rfl⟩ := hs₂
  obtain ⟨v₃, hv₃, rfl⟩ := hs₃
  obtain ⟨hb₁, hq₁⟩ := sphere_mem_lemma hv₁
  obtain ⟨hb₂, hq₂⟩ := sphere_mem_lemma hv₂
  obtain ⟨hb₃, hq₃⟩ := sphere_mem_lemma hv₃
  rw [cast_map, cast_map, cast_map] at heq
  obtain ⟨B, hB⟩ : ∃ B : ℤ, B = ((4 * L * d : ℕ) : ℤ) := ⟨_, rfl⟩
  rw [← hB] at heq
  have hL' : (1 : ℤ) ≤ L := by exact_mod_cast hL
  obtain ⟨hi1, hi2⟩ := abs_le.mp hiL
  obtain ⟨hj1, hj2⟩ := abs_le.mp hjL
  have hbound : ∀ m : Fin S, |j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m)| < B := by
    intro m
    have a1 : (v₁ m : ℤ) < d := by exact_mod_cast hb₁ m
    have a2 : (v₂ m : ℤ) < d := by exact_mod_cast hb₂ m
    have a3 : (v₃ m : ℤ) < d := by exact_mod_cast hb₃ m
    have z1 : (0 : ℤ) ≤ v₁ m := by positivity
    have z2 : (0 : ℤ) ≤ v₂ m := by positivity
    have z3 : (0 : ℤ) ≤ v₃ m := by positivity
    have hdpos : (1 : ℤ) ≤ d := by omega
    have f1 : (0 : ℤ) ≤ L - j := by linarith
    have f2 : (0 : ℤ) ≤ L + j := by linarith
    have f3 : (0 : ℤ) ≤ L - i := by linarith
    have f4 : (0 : ℤ) ≤ L + i := by linarith
    have g1 : (0 : ℤ) ≤ d + ((v₂ m : ℤ) - v₁ m) := by linarith
    have g2 : (0 : ℤ) ≤ d - ((v₂ m : ℤ) - v₁ m) := by linarith
    have g3 : (0 : ℤ) ≤ d + ((v₃ m : ℤ) - v₁ m) := by linarith
    have g4 : (0 : ℤ) ≤ d - ((v₃ m : ℤ) - v₁ m) := by linarith
    have hLd : (1 : ℤ) ≤ L * d := by nlinarith
    rw [hB]
    push_cast
    rw [abs_lt]
    constructor <;> nlinarith [mul_nonneg f1 g1, mul_nonneg f2 g2, mul_nonneg f1 g2,
      mul_nonneg f2 g1, mul_nonneg f3 g3, mul_nonneg f4 g4, mul_nonneg f3 g4, mul_nonneg f4 g3]
  have hsum : ∑ m, (j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m)) * B ^ (m : ℕ) = 0 := by
    have E : ∑ m, (j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m)) * B ^ (m : ℕ)
        = ∑ m, (j * ((v₂ m : ℤ) * B ^ (m : ℕ)) - j * ((v₁ m : ℤ) * B ^ (m : ℕ))
          - i * ((v₃ m : ℤ) * B ^ (m : ℕ)) + i * ((v₁ m : ℤ) * B ^ (m : ℕ))) :=
      Finset.sum_congr rfl (fun m _ => by ring)
    rw [E, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    linear_combination heq
  have hzero := coeff_zero B (fun m => j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m))
    hbound hsum
  have q₁ : ∑ m, ((v₁ m : ℕ) : ℤ) ^ 2 = (k : ℤ) := by exact_mod_cast hq₁
  have q₂ : ∑ m, ((v₂ m : ℕ) : ℤ) ^ 2 = (k : ℤ) := by exact_mod_cast hq₂
  have q₃ : ∑ m, ((v₃ m : ℕ) : ℤ) ^ 2 = (k : ℤ) := by exact_mod_cast hq₃
  have hrel := sphere_rel (fun m => (v₁ m : ℤ)) (fun m => (v₂ m : ℤ)) (fun m => (v₃ m : ℤ))
    (k : ℤ) q₁ q₂ q₃ i j (abs_pos.mp hj0) hij (fun m => by
      show j * ((v₂ m : ℤ) - v₁ m) = i * ((v₃ m : ℤ) - v₁ m)
      have h0 : j * ((v₂ m : ℤ) - v₁ m) - i * ((v₃ m : ℤ) - v₁ m) = 0 := hzero m
      linarith)
  have hv : v₂ = v₁ := funext fun m => Nat.cast_injective (congrFun hrel m)
  exact h12 (by rw [hv])
end Formalism.FrobeniusOrbits.ThickExists
