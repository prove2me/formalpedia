-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.ThickOrbit.key
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:12:15.78894+00:00
-- url     : https://prove2.me/submissions/14bdf682-98a3-4df5-8ce0-d52ceeac7129

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickOrbit
import Theorems.Thm_Formalism_FrobeniusOrbits_ThickOrbit_bound_aux

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Classical
open Formalism Formalism.FrobeniusOrbits
open Formalism.FrobeniusOrbits.ThickOrbit
namespace Formalism.FrobeniusOrbits.ThickOrbit
theorem _root_.solution {n L : ℕ} (T : Finset ℕ) (hT : ∀ s ∈ T, 4 * L * s < n) (hR : NoRel T L)
    (u₀ t h : ZMod n) (hord : 4 * L < addOrderOf h) (i₀ a b c : ℤ)
    (ha : a ∈ Finset.Ico i₀ (i₀ + L)) (hc : c ∈ Finset.Ico i₀ (i₀ + L)) (hab : a < b)
    (hbc : b < c) (hxa : InTranslate T u₀ (t + a • h)) (hxb : InTranslate T u₀ (t + b • h))
    (hxc : InTranslate T u₀ (t + c • h)) : False := by
  rw [Finset.mem_Ico] at ha hc
  obtain ⟨sa, hsa, ea⟩ := hxa
  obtain ⟨sb, hsb, eb⟩ := hxb
  obtain ⟨sc, hsc, ec⟩ := hxc
  rw [zsmul_eq_mul] at ea eb ec

  have hz : ∀ d : ℤ, 0 < d → d ≤ 4 * L → (d : ZMod n) * h ≠ 0 := by
    intro d hd hdL hdz
    have hdv : (addOrderOf h : ℤ) ∣ d :=
      addOrderOf_dvd_iff_zsmul_eq_zero.mpr (by rw [zsmul_eq_mul]; exact hdz)
    have := Int.le_of_dvd hd hdv
    omega
  have hab' : sa ≠ sb := by
    rintro rfl
    exact hz (b - a) (by omega) (by omega) (by push_cast; linear_combination eb - ea)
  have hac' : sa ≠ sc := by
    rintro rfl
    exact hz (c - a) (by omega) (by omega) (by push_cast; linear_combination ec - ea)
  have hbc' : sb ≠ sc := by
    rintro rfl
    exact hz (c - b) (by omega) (by omega) (by push_cast; linear_combination ec - eb)
  set X : ℤ := (c - a) * ((sb : ℤ) - sa) - (b - a) * ((sc : ℤ) - sa) with hX
  have hX0 : (X : ZMod n) = 0 := by
    rw [hX]; push_cast
    linear_combination (↑b - ↑a) * (ec - ea) - (↑c - ↑a) * (eb - ea)
  have hdvd : (n : ℤ) ∣ X := (ZMod.intCast_zmod_eq_zero_iff_dvd X n).mp hX0
  have h1 := bound_aux (c - a) sb (by omega) (hT sb hsb)
  have h2 := bound_aux (c - a) sa (by omega) (hT sa hsa)
  have h3 := bound_aux (b - a) sc (by omega) (hT sc hsc)
  have h4 := bound_aux (b - a) sa (by omega) (hT sa hsa)
  have p1 : 0 ≤ (c - a) * (sb : ℤ) := mul_nonneg (by omega) (by positivity)
  have p2 : 0 ≤ (c - a) * (sa : ℤ) := mul_nonneg (by omega) (by positivity)
  have p3 : 0 ≤ (b - a) * (sc : ℤ) := mul_nonneg (by omega) (by positivity)
  have p4 : 0 ≤ (b - a) * (sa : ℤ) := mul_nonneg (by omega) (by positivity)
  have habs : |X| < n := by
    rw [abs_lt, hX]
    constructor <;> nlinarith
  have hXz : X = 0 := Int.eq_zero_of_abs_lt_dvd hdvd habs
  refine hR sa hsa sb hsb sc hsc hab' hac' hbc' (b - a) (c - a) ?_ ?_ ?_ ?_ (by omega) ?_
  · rw [abs_pos]; omega
  · rw [abs_le]; constructor <;> omega
  · rw [abs_pos]; omega
  · rw [abs_le]; constructor <;> omega
  · rw [hX] at hXz; linarith
end Formalism.FrobeniusOrbits.ThickOrbit
