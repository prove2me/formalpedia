-- Prove2me | solution 1 for BesbesZeevi.Parametric.a19
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T08:13:36.625164+00:00
-- url     : https://prove2.me/submissions/4d583a28-a696-4f09-945e-b2b2adaa781f

import Mathlib
import Definitions.Def_BesbesZeevi_Parametric_Algorithm

open BesbesZeevi.Parametric in
theorem solution {k : ℕ} (D : Market) (F : Family k D)
    (S : OptimizerSelection D F) :
    ∀ θstar ∈ F.Θ, ∀ θhat ∈ F.Θ,
      0 ≤ S.pu θstar * F.demand (S.pu θstar) θstar -
            S.pu θhat * F.demand (S.pu θhat) θstar ∧
      S.pu θstar * F.demand (S.pu θstar) θstar -
            S.pu θhat * F.demand (S.pu θhat) θstar ≤
        2 * F.K2 * D.pHi * ‖θhat - θstar‖ := by
  intro θs hs θh hh
  have ha := S.pu_range θs hs
  have hb := S.pu_range θh hh
  refine ⟨sub_nonneg.mpr (S.pu_max θs hs _ hb), ?_⟩
  have hmid := S.pu_max θh hh _ ha
  have h1 := F.parameter_lipschitz _ ha θs hs θh hh
  have h2 := F.parameter_lipschitz _ hb θs hs θh hh
  rw [norm_sub_rev] at h1 h2
  have hlo := D.pLo_pos
  have hK := F.K2_pos
  have hn : 0 ≤ ‖θh - θs‖ := norm_nonneg _
  set a := S.pu θs
  set b := S.pu θh
  set e := F.K2 * ‖θh - θs‖
  have ha0 : 0 ≤ a := by linarith [ha.1]
  have hb0 : 0 ≤ b := by linarith [hb.1]
  have hA : a * (F.demand a θs - F.demand a θh) ≤ D.pHi * e := by
    have := (abs_le.mp h1).2
    calc a * (F.demand a θs - F.demand a θh) ≤ a * e := mul_le_mul_of_nonneg_left this ha0
      _ ≤ D.pHi * e := mul_le_mul_of_nonneg_right ha.2 (by positivity)
  have hB : b * (F.demand b θh - F.demand b θs) ≤ D.pHi * e := by
    have := (abs_le.mp h2).1
    calc b * (F.demand b θh - F.demand b θs) ≤ b * e :=
          mul_le_mul_of_nonneg_left (by linarith) hb0
      _ ≤ D.pHi * e := mul_le_mul_of_nonneg_right hb.2 (by positivity)
  have : 2 * F.K2 * D.pHi * ‖θh - θs‖ = 2 * (D.pHi * e) := by simp only [e]; ring
  rw [this]
  nlinarith [hA, hB, hmid]
