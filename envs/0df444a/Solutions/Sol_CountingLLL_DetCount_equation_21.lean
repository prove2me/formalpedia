-- Prove2me | solution 1 for CountingLLL.DetCount.equation_21
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T03:31:34.807612+00:00
-- url     : https://prove2.me/submissions/5985f246-bc03-4704-a45e-c116227ec287

import Definitions.Def_CountingLLL_DetCount_CSP

set_option autoImplicit false

/-- A ratio telescope remains valid across zero denominators when zero is absorbing. -/
private theorem ratio_telescope (a : ℕ → ℝ) (hzero : ∀ i, a i = 0 → a (i+1) = 0)
    (h0 : a 0 ≠ 0) (n : ℕ) : (∏ i ∈ Finset.range n, a (i+1) / a i) = a n / a 0 := by
  induction n with
  | zero =>
    simp [h0]
  | succ n ih =>
    rw [Finset.prod_range_succ, ih]
    by_cases h : a n = 0
    · simp [h, hzero n h]
    · field_simp

open CountingLLL.DetCount
open CSP

private noncomputable def pre (Φ : CSP) (e : Fin Φ.m ≃ Fin Φ.m) (i : ℕ) : Finset (Fin Φ.m) :=
  (Finset.univ.filter (fun j : Fin Φ.m => j.val < i)).image e

private lemma pre_zero (Φ : CSP) (e : Fin Φ.m ≃ Fin Φ.m) : pre Φ e 0 = ∅ := by
  classical
  simp [pre]

private lemma pre_full (Φ : CSP) (e : Fin Φ.m ≃ Fin Φ.m) : pre Φ e Φ.m = Finset.univ := by
  classical
  ext c
  simp only [pre, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
  exact ⟨e.symm c, (e.symm c).isLt, e.apply_symm_apply c⟩

private lemma pre_succ (Φ : CSP) (e : Fin Φ.m ≃ Fin Φ.m) (i : Fin Φ.m) :
    pre Φ e (i.val + 1) = insert (e i) (pre Φ e i.val) := by
  classical
  ext c
  simp only [pre, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj' : j.val ≤ i.val := Nat.lt_succ_iff.mp hj
    rcases eq_or_lt_of_le hj' with h | h
    · left; congr 1; exact Fin.ext h
    · exact Or.inr ⟨j, h, rfl⟩
  · rintro (rfl | ⟨j, hj, rfl⟩)
    · exact ⟨i, Nat.lt_succ_self _, rfl⟩
    · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩

private lemma pre_fresh (Φ : CSP) (e : Fin Φ.m ≃ Fin Φ.m) (i : Fin Φ.m) :
    e i ∉ pre Φ e i.val := by
  classical
  simp only [pre, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, not_exists]
  intro j h
  obtain ⟨hj, he⟩ := h
  have : j = i := e.injective he
  subst j
  exact Nat.lt_irrefl _ hj

private lemma pre_erase (Φ : CSP) (e : Fin Φ.m ≃ Fin Φ.m) (i : Fin Φ.m) :
    (pre Φ e (i.val + 1)).erase (e i) = pre Φ e i.val := by
  classical
  rw [pre_succ]
  simp [pre_fresh]

private lemma pre_mono (Φ : CSP) (e : Fin Φ.m ≃ Fin Φ.m) {i j : ℕ} (h : i ≤ j) :
    pre Φ e i ⊆ pre Φ e j := by
  classical
  apply Finset.image_mono
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact lt_of_lt_of_le hx h

private lemma z_antitone (Φ : CSP) {E F : Finset (Fin Φ.m)} (h : E ⊆ F) : Φ.Z F ≤ Φ.Z E := by
  classical
  apply Finset.card_le_card
  intro σ hσ
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ ⊢
  intro c hc
  exact hσ c (h hc)

private lemma z_zero_absorbs (Φ : CSP) (e : Fin Φ.m ≃ Fin Φ.m) (i : ℕ)
    (h : (Φ.Z (pre Φ e i) : ℝ) = 0) : (Φ.Z (pre Φ e (i+1)) : ℝ) = 0 := by
  have hz : Φ.Z (pre Φ e i) = 0 := Nat.cast_eq_zero.mp h
  have hle := z_antitone Φ (pre_mono Φ e (Nat.le_succ i))
  exact_mod_cast (Nat.eq_zero_of_le_zero (hz ▸ hle))

private lemma card_config_pos (Φ : CSP) : 0 < Fintype.card Φ.Config := by
  letI : Nonempty Φ.Config := ⟨fun v => ⟨0, lt_of_lt_of_le (by decide) (Φ.two_le_q v)⟩⟩
  exact Fintype.card_pos

private lemma z_empty (Φ : CSP) : Φ.Z ∅ = Fintype.card Φ.Config := by
  classical
  unfold CSP.Z
  rw [show Finset.univ.filter (Φ.SatAll ∅) = Finset.univ by ext σ; simp [CSP.SatAll]]
  simp

private lemma prob_satall (Φ : CSP) (E : Finset (Fin Φ.m)) :
    Φ.prob (Φ.SatAll E) = (Φ.Z E : ℝ) / Fintype.card Φ.Config := by
  rfl

private lemma prob_step (Φ : CSP) (e : Fin Φ.m ≃ Fin Φ.m) (i : Fin Φ.m) :
    Φ.prob (fun σ => Φ.Sat (e i) σ ∧ Φ.SatAll (pre Φ e i.val) σ) =
      (Φ.Z (pre Φ e (i.val+1)) : ℝ) / Fintype.card Φ.Config := by
  classical
  rw [pre_succ]
  unfold CSP.prob CSP.Z
  congr 1
  congr 1
  apply congrArg Finset.card
  apply Finset.ext
  intro σ
  letI : DecidablePred (fun σ : Φ.Config => Φ.Sat (e i) σ ∧ Φ.SatAll (pre Φ e i.val) σ) := fun _ => Classical.propDecidable _
  letI : DecidablePred (Φ.SatAll (insert (e i) (pre Φ e i.val))) := fun _ => Classical.propDecidable _
  constructor
  · intro h
    have hh := (Finset.mem_filter.mp h).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [CSP.SatAll] using hh
  · intro h
    have hh := (Finset.mem_filter.mp h).2
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa [CSP.SatAll] using hh

private lemma cond_step (Φ : CSP) (e : Fin Φ.m ≃ Fin Φ.m) (i : Fin Φ.m) :
    Φ.condProb (Φ.Sat (e i)) (Φ.SatAll (pre Φ e i.val)) =
      (Φ.Z (pre Φ e (i.val+1)) : ℝ) / (Φ.Z (pre Φ e i.val) : ℝ) := by
  rw [CSP.condProb, prob_step, prob_satall]
  exact div_div_div_cancel_right₀ (by exact_mod_cast (ne_of_gt (card_config_pos Φ))) _ _

private lemma ratio_products (Φ : CSP) (e : Fin Φ.m ≃ Fin Φ.m) :
    (∏ i : Fin Φ.m, Φ.condProb (Φ.Sat (e i)) (Φ.SatAll (pre Φ e i.val))) =
      (Φ.ZPhi : ℝ) / Fintype.card Φ.Config := by
  let a : ℕ → ℝ := fun i => (Φ.Z (pre Φ e i) : ℝ)
  have ha0 : a 0 = (Fintype.card Φ.Config : ℝ) := by
    simp [a, pre_zero, z_empty]
  have h0 : a 0 ≠ 0 := by rw [ha0]; exact_mod_cast (ne_of_gt (card_config_pos Φ))
  have ht := ratio_telescope a (z_zero_absorbs Φ e) h0 Φ.m
  have hf : (∏ i : Fin Φ.m, a (i.val+1) / a i.val) = a Φ.m / a 0 := by
    calc
      (∏ i : Fin Φ.m, a (i.val+1) / a i.val) = ∏ i ∈ Finset.range Φ.m, a (i+1) / a i := by
        exact Fin.prod_univ_eq_prod_range (fun j => a (j+1) / a j) Φ.m
      _ = a Φ.m / a 0 := ht
  calc
    (∏ i : Fin Φ.m, Φ.condProb (Φ.Sat (e i)) (Φ.SatAll (pre Φ e i.val))) =
        ∏ i : Fin Φ.m, a (i.val+1) / a i.val := by
          apply Finset.prod_congr rfl
          intro i hi
          exact cond_step Φ e i
    _ = a Φ.m / a 0 := hf
    _ = (Φ.ZPhi : ℝ) / Fintype.card Φ.Config := by simp [a, pre_full, ha0, CSP.ZPhi]

private lemma r_step (Φ : CSP) (e : Fin Φ.m ≃ Fin Φ.m) (i : Fin Φ.m) :
    1 - Φ.r (pre Φ e (i.val+1)) (e i) =
      (Φ.Z (pre Φ e (i.val+1)) : ℝ) / (Φ.Z (pre Φ e i.val) : ℝ) := by
  rw [CSP.r, pre_erase]
  ring

theorem solution (Φ : CSP) (hΦ : Φ.Condition11) (e : Fin Φ.m ≃ Fin Φ.m) :
    let Cpre : ℕ → Finset (Fin Φ.m) :=
      fun i => (Finset.univ.filter (fun j : Fin Φ.m => j.val < i)).image e
    (Φ.ZPhi : ℝ) = (∏ v, (Φ.q v : ℝ)) * Φ.prob (Φ.SatAll Finset.univ) ∧
    (∏ v, (Φ.q v : ℝ)) * Φ.prob (Φ.SatAll Finset.univ) =
      (∏ v, (Φ.q v : ℝ)) * ∏ i : Fin Φ.m, Φ.condProb (Φ.Sat (e i)) (Φ.SatAll (Cpre i.val)) ∧
    (∏ v, (Φ.q v : ℝ)) * ∏ i : Fin Φ.m, Φ.condProb (Φ.Sat (e i)) (Φ.SatAll (Cpre i.val)) =
      (∏ v, (Φ.q v : ℝ)) * ∏ i : Fin Φ.m, (1 - Φ.r (Cpre (i.val + 1)) (e i)) := by
  change (Φ.ZPhi : ℝ) = (∏ v, (Φ.q v : ℝ)) * Φ.prob (Φ.SatAll Finset.univ) ∧
    (∏ v, (Φ.q v : ℝ)) * Φ.prob (Φ.SatAll Finset.univ) =
      (∏ v, (Φ.q v : ℝ)) * ∏ i : Fin Φ.m, Φ.condProb (Φ.Sat (e i)) (Φ.SatAll (pre Φ e i.val)) ∧
    (∏ v, (Φ.q v : ℝ)) * ∏ i : Fin Φ.m, Φ.condProb (Φ.Sat (e i)) (Φ.SatAll (pre Φ e i.val)) =
      (∏ v, (Φ.q v : ℝ)) * ∏ i : Fin Φ.m, (1 - Φ.r (pre Φ e (i.val + 1)) (e i))
  have hcard : (Fintype.card Φ.Config : ℝ) = ∏ v, (Φ.q v : ℝ) := by
    rw [Fintype.card_pi]
    simp
  have hn : (Fintype.card Φ.Config : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (card_config_pos Φ))
  have hprods : (∏ i : Fin Φ.m, Φ.condProb (Φ.Sat (e i)) (Φ.SatAll (pre Φ e i.val))) =
      ∏ i : Fin Φ.m, (1 - Φ.r (pre Φ e (i.val + 1)) (e i)) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [cond_step, r_step]
  constructor
  · rw [prob_satall, ← hcard]
    unfold CSP.ZPhi
    field_simp
  constructor
  · rw [prob_satall, ratio_products]
    rfl
  · rw [hprods]
