-- Prove2me | solution 1 for DeMorganApprox.Main.lemma_5_7
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T17:15:17.302579+00:00
-- url     : https://prove2.me/submissions/486c0406-4330-499a-b6ea-0f7012bd2555

import Theorems.Thm_DeMorganApprox_Main_lemma_5_2
import Theorems.Thm_DeMorganApprox_Main_lemma_5_6

open DeMorganApprox.Main

private theorem chainInduction {m : ℕ} (G : TieRule → Formula m → Prop)
    (base : ∀ tie i b, G tie (.lit i b))
    (step : ∀ tie T, T.isLeaf = false →
      (∀ t ∈ terminals tie T, G t.1 t.2) → G tie T)
    (T : Formula m) (tie : TieRule) : G tie T := by
  suffices strong : ∀ tie, G tie T ∧ ∀ t ∈ terminals tie T, G t.1 t.2 from (strong tie).1
  induction T with
  | lit i b =>
    intro tie
    exact ⟨base tie i b, by simpa [terminals] using base tie i b⟩
  | and l r ihl ihr | or l r ihl ihr =>
    intro tie
    suffices aux : ∀ t ∈ terminals tie _, G t.1 t.2 from ⟨step tie _ rfl aux, aux⟩
    cases hd : heavyDir tie l r <;> simp [terminals, hd, pick, ihl, ihr] <;>
      intro a b h <;> first | exact (ihl _).2 (a,b) h | exact (ihr _).2 (a,b) h

private theorem leafPos {m : ℕ} (T : Formula m) : 0 < T.leaves := by
  induction T <;> simp_all [Formula.leaves] <;> omega

private theorem partition {m : ℕ} (T : Formula m) (tie : TieRule) :
    ((terminals tie T).map (fun t => t.2.leaves)).sum = T.leaves ∧
    ∀ t ∈ terminals tie T, 2 * t.2.leaves ≤ max 2 T.leaves := by
  induction T generalizing tie with
  | lit i b => simp [terminals, Formula.leaves]
  | and l r ihl ihr | or l r ihl ihr =>
    have hl := leafPos l
    have hr := leafPos r
    have hd₀ : heavyDir tie l r = false → r.leaves ≤ l.leaves := by
      simp only [heavyDir]; split_ifs <;> simp_all <;> omega
    have hd₁ : heavyDir tie l r = true → l.leaves ≤ r.leaves := by
      simp only [heavyDir]; split_ifs <;> simp_all <;> omega
    constructor
    · cases hd : heavyDir tie l r <;>
        simp [terminals, hd, pick, (ihl _).1, (ihr _).1, Formula.leaves, Nat.add_comm]
    · intro t ht
      cases hd : heavyDir tie l r
      · simp only [terminals, hd, Bool.not_false, pick, if_true, Bool.false_eq_true, if_false,
          List.mem_cons] at ht
        rcases ht with rfl | h
        · simp only [Formula.leaves]; have := hd₀ hd; omega
        · have := (ihl _).2 t h; simp only [Formula.leaves]; omega
      · simp only [terminals, hd, Bool.not_true, pick, if_true, Bool.false_eq_true, if_false,
          List.mem_cons] at ht
        rcases ht with rfl | h
        · simp only [Formula.leaves]; have := hd₁ hd; omega
        · have := (ihr _).2 t h; simp only [Formula.leaves]; omega

private theorem termEstimate (N a S : ℝ) (ha : 1 ≤ a) (hN : 2*a ≤ N)
    (hs : 0 ≤ S) (hb : S ≤ 100 * Real.sqrt a - 5) :
    S^2 + S ≤ (10000 - 1200 / Real.sqrt N) * a := by
  have hp : 0 < Real.sqrt N := Real.sqrt_pos.2 (by linarith)
  have hq : 1 ≤ Real.sqrt a := by simpa using Real.sqrt_le_sqrt ha
  have hqa := Real.sq_sqrt (by linarith : 0 ≤ a)
  have hqn := Real.sq_sqrt (by linarith : 0 ≤ N)
  have hsmall : 15 * Real.sqrt a ≤ 11 * Real.sqrt N := by
    by_contra! h
    have hpos := mul_pos (sub_pos.mpr h) (show 0 < 15 * Real.sqrt a + 11 * Real.sqrt N by positivity)
    nlinarith only [hqa,hqn,hN,hpos]
  have hh := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ 80 * Real.sqrt a by positivity)
  have hs2 := mul_self_le_mul_self hs hb
  have hmain : S^2 + S ≤ 10000*a - 880*Real.sqrt a := by nlinarith
  have hdr : 1200*a / Real.sqrt N ≤ 880*Real.sqrt a :=
    (div_le_iff₀ hp).2 (by nlinarith only [hh,hqa])
  calc
    _ ≤ 10000*a - 880*Real.sqrt a := hmain
    _ ≤ 10000*a - 1200*a / Real.sqrt N := by linarith
    _ = _ := by ring

private theorem sumEstimate {α : Type} (f g : α → ℝ) (c : ℝ) (xs : List α)
    (h : ∀ x ∈ xs, f x ≤ c * g x) : (xs.map f).sum ≤ c * (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simpa [List.map_cons, List.sum_cons, mul_add] using
      add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

private theorem castSum {α : Type} (g : α → ℕ) (xs : List α) :
    (xs.map (fun t => (g t : ℝ))).sum = ((xs.map g).sum : ℕ) := by
  induction xs <;> simp_all

private theorem bounds {m : ℕ} (T : Formula m) (tie : TieRule) :
    ((program tie T).IsVectorForm ∧ (program tie T).Computes T.eval ∧
      (program tie T).HasBalancedBound (helperBound tie T)) ∧
      helperBound tie T ≤ 100 * Real.sqrt T.leaves - 5 := by
  apply chainInduction (fun tie T => ((program tie T).IsVectorForm ∧
    (program tie T).Computes T.eval ∧ (program tie T).HasBalancedBound (helperBound tie T)) ∧
      helperBound tie T ≤ 100 * Real.sqrt T.leaves - 5)
  · intro tie i b
    obtain ⟨hc,hv,hw,_⟩ := lemma_5_2 tie i b
    exact ⟨⟨hv,hc,hw⟩, by norm_num [helperBound, helperBoundOf, Formula.isLeaf, Formula.leaves]⟩
  · intro tie U hu ih
    obtain ⟨hc,hv,_,hw,he⟩ := lemma_5_6 tie U hu (fun t ht => (ih t ht).1)
    refine ⟨⟨hv,hc,hw⟩, ?_⟩
    have hn : 2 ≤ U.leaves := by
      cases U with
      | lit i b => simp [Formula.isLeaf] at hu
      | and l r | or l r =>
        simp only [Formula.leaves]
        have := leafPos l
        have := leafPos r
        omega
    let N : ℝ := U.leaves
    have hn' : 1 ≤ N := by dsimp [N]; exact_mod_cast (show 1 ≤ U.leaves by omega)
    have hq : 1 ≤ Real.sqrt N := by simpa using Real.sqrt_le_sqrt hn'
    have hss := Real.sq_sqrt (show 0 ≤ N by linarith)
    have hp : Real.sqrt N ≠ 0 := by linarith
    obtain ⟨hpart,hhalf⟩ := partition U tie
    have hs := sumEstimate (fun t : TieRule × Formula m => helperBound t.1 t.2 ^ 2 + helperBound t.1 t.2)
      (fun t => (t.2.leaves : ℝ)) (10000 - 1200 / Real.sqrt N) (terminals tie U) (by
        intro t h
        apply termEstimate
        · exact_mod_cast leafPos t.2
        · have hle := hhalf t h
          rw [max_eq_right hn] at hle
          dsimp [N]
          exact_mod_cast hle
        · exact le_trans (by norm_num) (ih t h).1.2.2.1
        · exact (ih t h).2)
    rw [castSum (fun t : TieRule × Formula m => t.2.leaves), hpart] at hs
    change _ ≤ (10000 - 1200 / Real.sqrt N) * N at hs
    have hid : (10000 - 1200 / Real.sqrt N) * N = 10000 * N - 1200 * Real.sqrt N := by
      field_simp; nlinarith
    rw [hid] at hs
    have hfinal := Real.sqrt_le_sqrt (show _ ≤ (100 * Real.sqrt N - 6)^2 by
      exact hs.trans (by nlinarith))
    rw [Real.sqrt_sq (by linarith : 0 ≤ 100 * Real.sqrt N - 6)] at hfinal
    rw [he]
    change 1 + _ ≤ 100 * Real.sqrt N - 5
    linarith

theorem solution :
    (∀ (m : ℕ) (tie : TieRule) (T : Formula m), T.isLeaf = false →
      helperBound tie T ≤ 100 * Real.sqrt (T.leaves : ℝ) - 5) ∧
    (∀ (m : ℕ) (tie : TieRule) (T : Formula m),
      (program tie T).HasBalancedBound (helperBound tie T) ∧
        helperBound tie T ≤ 100 * Real.sqrt (T.leaves : ℝ)) :=
  ⟨fun _ tie T _ => (bounds T tie).2, fun _ tie T =>
    ⟨(bounds T tie).1.2.2, by linarith [(bounds T tie).2]⟩⟩
