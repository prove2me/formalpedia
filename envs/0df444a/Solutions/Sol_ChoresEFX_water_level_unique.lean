-- Prove2me | solution 1 for ChoresEFX.water_level_unique
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-14T04:30:11.247463+00:00
-- url     : https://prove2.me/submissions/757da3eb-6bad-4a4b-9d8b-42e1c3f36692

import Mathlib

theorem solution {κ : Type*} [Fintype κ] (n : ℕ) (hn : 0 < n) (β : ℝ) (hβ : 0 < β)
    (r : κ → ℝ) (hr : ∀ g, 0 < r g) (hmβ : (n : ℝ) < (Fintype.card κ : ℝ) * β) :
    ∃! s : ℝ, 0 < s ∧ ∑ g, min (s * r g) β = (n : ℝ) := by
  classical
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hκpos : 0 < Fintype.card κ := by
    rcases Nat.eq_zero_or_pos (Fintype.card κ) with h | h
    · have h0 : (Fintype.card κ : ℝ) = 0 := by exact_mod_cast h
      rw [h0, zero_mul] at hmβ
      linarith
    · exact h
  have hκ : Nonempty κ := Fintype.card_pos_iff.mp hκpos
  let F : ℝ → ℝ := fun s => ∑ g, min (s * r g) β
  have hF0 : F 0 = 0 := by
    simp [F, hβ.le]
  have hFcont : Continuous F := by
    dsimp [F]
    continuity
  -- choose a level beyond saturation
  let S : ℝ := (∑ g, β / r g) + 1
  have hSpos : 0 < S := by
    have hnn : 0 ≤ ∑ g, β / r g :=
      Finset.sum_nonneg (fun g _ => div_nonneg hβ.le (hr g).le)
    dsimp [S]
    linarith
  have hSle : ∀ g, β / r g ≤ S := by
    intro g
    have hterm : β / r g ≤ ∑ g', β / r g' :=
      Finset.single_le_sum (fun g' _ => div_nonneg hβ.le (hr g').le) (Finset.mem_univ g)
    dsimp [S]
    linarith
  have hFS : F S = (Fintype.card κ : ℝ) * β := by
    have hmin : ∀ g, min (S * r g) β = β := by
      intro g
      exact min_eq_right ((div_le_iff₀ (hr g)).mp (hSle g))
    dsimp [F]
    calc ∑ g, min (S * r g) β = ∑ _g : κ, β :=
          Finset.sum_congr rfl (fun g _ => hmin g)
      _ = (Fintype.card κ : ℝ) * β := by
          rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  -- existence by the intermediate value theorem
  obtain ⟨s, hsIcc, hsF⟩ :=
    intermediate_value_Icc (le_of_lt hSpos) hFcont.continuousOn
      (show (n : ℝ) ∈ Set.Icc (F 0) (F S) from
        ⟨by rw [hF0]; exact hnR.le, by rw [hFS]; exact hmβ.le⟩)
  have hs0 : 0 < s := by
    rcases le_or_gt s 0 with h | h
    · have hs : s = 0 := le_antisymm h hsIcc.1
      rw [hs, hF0] at hsF
      linarith
    · exact h
  refine ⟨s, ⟨hs0, by simpa [F] using hsF⟩, ?_⟩
  -- uniqueness
  have no_lt : ∀ a b : ℝ, 0 < a → 0 < b → F a = (n : ℝ) → F b = (n : ℝ) → ¬ a < b := by
    intro a b ha hb haF hbF hab
    have hle : ∀ g, min (a * r g) β ≤ min (b * r g) β := by
      intro g
      exact min_le_min (mul_le_mul_of_nonneg_right hab.le (hr g).le) le_rfl
    by_cases hex : ∃ g, b * r g < β
    · obtain ⟨g, hg⟩ := hex
      have hstrict : min (a * r g) β < min (b * r g) β := by
        have h1 : a * r g < b * r g := mul_lt_mul_of_pos_right hab (hr g)
        rw [min_eq_left (le_of_lt (lt_trans h1 hg)), min_eq_left (le_of_lt hg)]
        exact h1
      have hlt : F a < F b :=
        Finset.sum_lt_sum (fun g _ => hle g) ⟨g, Finset.mem_univ _, hstrict⟩
      linarith
    · push Not at hex
      have hbval : F b = (Fintype.card κ : ℝ) * β := by
        dsimp [F]
        calc ∑ g, min (b * r g) β = ∑ _g : κ, β :=
              Finset.sum_congr rfl (fun g _ => min_eq_right (hex g))
          _ = (Fintype.card κ : ℝ) * β := by
              rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
      linarith
  intro y hy
  have hy0 : 0 < y := hy.1
  have hyF : F y = (n : ℝ) := by simpa [F] using hy.2
  exact le_antisymm (le_of_not_gt (no_lt s y hs0 hy0 hsF hyF))
    (le_of_not_gt (no_lt y s hy0 hs0 hyF hsF))
