-- Prove2me | solution 1 for FoundationsRL.GeneralDM.e2d_general_regret_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-01T19:23:10.238124+00:00
-- url     : https://prove2.me/submissions/538dabe7-b15e-429e-a0dd-95265344f64d

import Mathlib
import Definitions.Def_FoundationsRL_GeneralDM_Protocol
import Definitions.Def_FoundationsRL_GeneralDM_Divergences
import Definitions.Def_FoundationsRL_GeneralDM_DEC

set_option autoImplicit false

namespace Cex7f4cebdb
open FoundationsRL.GeneralDM

/-- reward coordinate is `false`, information coordinate is `true` -/
noncomputable def rw : Bool → ℝ := fun y => if y then 0 else 1

noncomputable def A (s t : ℝ) : Bool → Bool → ℝ := fun π y =>
  if π then (if y then t ^ 2 else 0) else (if y then s ^ 2 else -s ^ 2)

noncomputable def B (s t : ℝ) : Bool → Bool → ℝ := fun π y => A s t (!π) y

def M : Set (Bool → Bool → ℝ) := {m | ∃ s t : ℝ, m = A s t ∨ m = B s t}

noncomputable def mh (c : ℝ) : Bool → Bool → ℝ := fun _ y => if y then c ^ 2 else 0

noncomputable def ps (m : Bool → Bool → ℝ) : Bool :=
  if fM rw m false ≤ fM rw m true then true else false

theorem hps : ∀ m, ∀ π, fM rw m π ≤ fM rw m (ps m) := by
  intro m π
  by_cases h : fM rw m false ≤ fM rw m true
  · cases π <;> simp [ps, h]
  · have h' := (not_le.mp h).le
    cases π <;> simp [ps, h, h']

theorem sqrt_negsq (s : ℝ) : Real.sqrt (-s ^ 2) = 0 :=
  Real.sqrt_eq_zero'.mpr (by nlinarith [sq_nonneg s])

theorem fA_true (s t : ℝ) : fM rw (A s t) true = 0 := by
  simp [fM, A, rw, Fintype.sum_bool]
theorem fA_false (s t : ℝ) : fM rw (A s t) false = -s ^ 2 := by
  simp [fM, A, rw, Fintype.sum_bool]
theorem fB_true (s t : ℝ) : fM rw (B s t) true = -s ^ 2 := by
  simp [fM, B, A, rw, Fintype.sum_bool]
theorem fB_false (s t : ℝ) : fM rw (B s t) false = 0 := by
  simp [fM, B, A, rw, Fintype.sum_bool]

theorem hA_true (s t c : ℝ) : hellingerSq (A s t true) (mh c true) = (|t| - |c|) ^ 2 := by
  simp [hellingerSq, A, mh, Fintype.sum_bool, Real.sqrt_sq_eq_abs]
theorem hA_false (s t c : ℝ) : hellingerSq (A s t false) (mh c false) = (|s| - |c|) ^ 2 := by
  simp [hellingerSq, A, mh, Fintype.sum_bool, Real.sqrt_sq_eq_abs, sqrt_negsq]
theorem hB_true (s t c : ℝ) : hellingerSq (B s t true) (mh c true) = (|s| - |c|) ^ 2 := by
  simp [hellingerSq, B, A, mh, Fintype.sum_bool, Real.sqrt_sq_eq_abs, sqrt_negsq]
theorem hB_false (s t c : ℝ) : hellingerSq (B s t false) (mh c false) = (|t| - |c|) ^ 2 := by
  simp [hellingerSq, B, A, mh, Fintype.sum_bool, Real.sqrt_sq_eq_abs]

theorem fps0 : ∀ m ∈ M, fM rw m (ps m) = 0 := by
  rintro m ⟨s, t, rfl | rfl⟩
  · have key : ∀ b, fM rw (A s t) b ≤ 0 := by
      intro b; cases b
      · rw [fA_false]; nlinarith [sq_nonneg s]
      · rw [fA_true]
    exact le_antisymm (key _) (by simpa [fA_true] using hps (A s t) true)
  · have key : ∀ b, fM rw (B s t) b ≤ 0 := by
      intro b; cases b
      · rw [fB_false]
      · rw [fB_true]; nlinarith [sq_nonneg s]
    exact le_antisymm (key _) (by simpa [fB_false] using hps (B s t) false)

noncomputable def pay (p : Bool → ℝ) (c : ℝ) (m : Bool → Bool → ℝ) : ℝ :=
  ∑ π, p π * (fM rw m (ps m) - fM rw m π - 2 * hellingerSq (m π) (mh c π))

theorem upper (p : Bool → ℝ) (hp0 : ∀ π, 0 ≤ p π) (c : ℝ) (hc : 0 ≤ c) :
    ∀ m ∈ M, pay p c m ≤ 2 * c ^ 2 * p false ∨ pay p c m ≤ 2 * c ^ 2 * p true := by
  have h1 := hp0 true
  have h2 := hp0 false
  rintro m hm
  have h0 := fps0 m hm
  obtain ⟨s, t, rfl | rfl⟩ := hm
  · left
    simp only [pay, Fintype.sum_bool, h0, fA_true, fA_false, hA_true, hA_false, abs_of_nonneg hc]
    have e : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    nlinarith [mul_nonneg h1 (sq_nonneg (|t| - c)), mul_nonneg h2 (sq_nonneg (|s| - 2 * c))]
  · right
    simp only [pay, Fintype.sum_bool, h0, fB_true, fB_false, hB_true, hB_false, abs_of_nonneg hc]
    have e : s ^ 2 = |s| ^ 2 := (sq_abs s).symm
    nlinarith [mul_nonneg h2 (sq_nonneg (|t| - c)), mul_nonneg h1 (sq_nonneg (|s| - 2 * c))]

theorem lower (p : Bool → ℝ) (hp0 : ∀ π, 0 ≤ p π) (hp1 : ∑ π, p π = 1) (c : ℝ) (hc : 0 ≤ c) :
    ∃ m ∈ M, c ^ 2 ≤ pay p c m := by
  rw [Fintype.sum_bool] at hp1
  have h2c : |2 * c| = 2 * c := abs_of_nonneg (by linarith)
  by_cases hf : 1 / 2 ≤ p false
  · refine ⟨A (2 * c) c, ⟨2 * c, c, Or.inl rfl⟩, ?_⟩
    have h0 := fps0 _ ⟨2 * c, c, Or.inl rfl⟩
    simp only [pay, Fintype.sum_bool, h0, fA_true, fA_false, hA_true, hA_false,
      abs_of_nonneg hc, h2c]
    nlinarith [sq_nonneg c]
  · refine ⟨B (2 * c) c, ⟨2 * c, c, Or.inr rfl⟩, ?_⟩
    have h0 := fps0 _ ⟨2 * c, c, Or.inr rfl⟩
    simp only [pay, Fintype.sum_bool, h0, fB_true, fB_false, hB_true, hB_false,
      abs_of_nonneg hc, h2c]
    nlinarith [sq_nonneg c]

theorem dec_ge (c : ℝ) (hc : 0 ≤ c) : c ^ 2 ≤ decGf M rw ps 2 (mh c) := by
  unfold decGf
  apply le_csInf
  · refine ⟨_, ⟨fun _ => 1 / 2, ⟨fun _ => by norm_num, ?_⟩, rfl⟩⟩
    simp
  · rintro _ ⟨p, hp, rfl⟩
    obtain ⟨m, hm, hle⟩ := lower p hp.1 hp.2 c hc
    have hs := hp.2
    rw [Fintype.sum_bool] at hs
    have h1 := hp.1 true
    have h2 := hp.1 false
    refine le_trans hle (le_csSup ⟨2 * c ^ 2, ?_⟩ ⟨m, hm, rfl⟩)
    rintro _ ⟨m', hm', rfl⟩
    have hc2 := sq_nonneg c
    rcases upper p hp.1 c hc m' hm' with h | h
    · change pay p c m' ≤ 2 * c ^ 2
      nlinarith
    · change pay p c m' ≤ 2 * c ^ 2
      nlinarith

theorem nbdd : ¬ BddAbove (decGf M rw ps 2 '' Set.range (fun n : ℕ => mh n)) := by
  rintro ⟨K, hK⟩
  obtain ⟨n, hn⟩ := exists_nat_gt K
  have h1 := hK ⟨mh ((n + 1 : ℕ) : ℝ), ⟨n + 1, rfl⟩, rfl⟩
  have h2 := dec_ge ((n + 1 : ℕ) : ℝ) (Nat.cast_nonneg _)
  push_cast at h1 h2
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

theorem cex : ¬ (∀ {S Y : Type} [Fintype S] [Fintype Y]
    (𝓜 : Set (S → Y → ℝ)) (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S)
    (hpiStar : ∀ m, ∀ π, fM rew m π ≤ fM rew m (piStar m))
    (γ : ℝ) (hγ : 0 < γ)
    (mstar : S → Y → ℝ) (hmstar : mstar ∈ 𝓜)
    (T : ℕ) (p : Fin T → S → ℝ) (hp : ∀ t, (∀ π, 0 ≤ p t π) ∧ ∑ π, p t π = 1)
    (mhat : Fin T → S → Y → ℝ) (hatM : Set (S → Y → ℝ)) (hhatM : ∀ t, mhat t ∈ hatM)
    (hE2D : ∀ t, ∀ m ∈ 𝓜, ∑ π, p t π *
        (fM rew m (piStar m) - fM rew m π - γ * hellingerSq (m π) (mhat t π)) ≤
      decGf 𝓜 rew piStar γ (mhat t)),
    regret (fM rew mstar) (piStar mstar) T p ≤
      (sSup ((decGf 𝓜 rew piStar γ) '' hatM)) * T +
      γ * ∑ t : Fin T, ∑ π, p t π * hellingerSq (mstar π) (mhat t π)) := by
  intro h
  have hmA : A 2 1 ∈ M := ⟨2, 1, Or.inl rfl⟩
  have hE : ∀ t : Fin 1, ∀ m ∈ M, ∑ π, (fun (_ : Fin 1) (_ : Bool) => (1 / 2 : ℝ)) t π *
      (fM rw m (ps m) - fM rw m π - 2 * hellingerSq (m π) ((fun _ => mh 1) t π)) ≤
      decGf M rw ps 2 ((fun (_ : Fin 1) => mh 1) t) := by
    intro t m hm
    have hd := dec_ge 1 (by norm_num)
    have hu := upper (fun _ => (1 / 2 : ℝ)) (fun _ => by norm_num) 1 (by norm_num) m hm
    change pay (fun _ => (1 / 2 : ℝ)) 1 m ≤ decGf M rw ps 2 (mh 1)
    rcases hu with hu | hu <;> norm_num at hu hd <;> linarith
  have key := h (S := Bool) (Y := Bool) M rw ps hps 2 (by norm_num) (A 2 1) hmA 1
    (fun _ _ => 1 / 2) (fun _ => ⟨fun _ => by norm_num, by simp⟩)
    (fun _ => mh 1) (Set.range (fun n : ℕ => mh n)) (fun _ => ⟨1, by simp⟩) hE
  rw [Real.sSup_of_not_bddAbove nbdd] at key
  have h0 := fps0 _ hmA
  simp only [regret, Fintype.sum_bool, h0, fA_true, fA_false, hA_true, hA_false,
    Finset.univ_unique, Finset.sum_singleton] at key
  norm_num at key

end Cex7f4cebdb

open FoundationsRL.GeneralDM in
theorem solution : ¬ (∀ {S Y : Type} [Fintype S] [Fintype Y]
    (𝓜 : Set (S → Y → ℝ)) (rew : Y → ℝ) (piStar : (S → Y → ℝ) → S)
    (hpiStar : ∀ m, ∀ π, fM rew m π ≤ fM rew m (piStar m))
    (γ : ℝ) (hγ : 0 < γ)
    (mstar : S → Y → ℝ) (hmstar : mstar ∈ 𝓜)
    (T : ℕ) (p : Fin T → S → ℝ) (hp : ∀ t, (∀ π, 0 ≤ p t π) ∧ ∑ π, p t π = 1)
    (mhat : Fin T → S → Y → ℝ) (hatM : Set (S → Y → ℝ)) (hhatM : ∀ t, mhat t ∈ hatM)
    (hE2D : ∀ t, ∀ m ∈ 𝓜, ∑ π, p t π *
        (fM rew m (piStar m) - fM rew m π - γ * hellingerSq (m π) (mhat t π)) ≤
      decGf 𝓜 rew piStar γ (mhat t)),
    regret (fM rew mstar) (piStar mstar) T p ≤
      (sSup ((decGf 𝓜 rew piStar γ) '' hatM)) * T +
      γ * ∑ t : Fin T, ∑ π, p t π * hellingerSq (mstar π) (mhat t π)) := by
  exact Cex7f4cebdb.cex
