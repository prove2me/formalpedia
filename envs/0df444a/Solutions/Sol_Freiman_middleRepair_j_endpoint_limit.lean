-- Prove2me | solution 1 for Freiman.middleRepair_j_endpoint_limit
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T10:07:48.204872+00:00
-- url     : https://prove2.me/submissions/51b8bc28-f047-4265-a1e5-4ef848cadeb4

import Definitions.Def_Freiman_middleRepair
import Theorems.Thm_Freiman_prefixEval_cylinder_bound
import Theorems.Thm_Freiman_cylinder_bound_tendsto
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.SplitIfs

open Freiman

namespace M8Sep10JEndpoint

private lemma pe_nonneg (w : List ℕ+) (x : ℝ) (hx : 0 ≤ x) : 0 ≤ prefixEval w x := by
  induction w with
  | nil => exact hx
  | cons a w ih =>
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    change 0 ≤ 1 / (((a:ℕ):ℝ) + prefixEval w x)
    positivity

private lemma pe_append (u v : List ℕ+) (x : ℝ) :
    prefixEval (u ++ v) x = prefixEval u (prefixEval v x) := by
  induction u with
  | nil => rfl
  | cons a u ih => simp only [List.cons_append, prefixEval, ih]

private lemma pe_order (w : List ℕ+) (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≤ y) :
    (w.length % 2 = 0 → prefixEval w x ≤ prefixEval w y) ∧
    (w.length % 2 = 1 → prefixEval w y ≤ prefixEval w x) := by
  induction w with
  | nil => simp [prefixEval, hxy]
  | cons a w ih =>
    have ha : (0:ℝ) < ((a:ℕ):ℝ) := by exact_mod_cast a.pos
    have hpx := pe_nonneg w x hx
    have hpy := pe_nonneg w y hy
    constructor
    · intro h
      have hw : w.length % 2 = 1 := by simp only [List.length_cons] at h; omega
      exact one_div_le_one_div_of_le (by linarith : 0 < ((a:ℕ):ℝ)+prefixEval w y)
        (by linarith only [ih.2 hw])
    · intro h
      have hw : w.length % 2 = 0 := by simp only [List.length_cons] at h; omega
      exact one_div_le_one_div_of_le (by linarith : 0 < ((a:ℕ):ℝ)+prefixEval w x)
        (by linarith only [ih.1 hw])

private lemma alpha_beta_bounds :
    (1/4:ℝ) ≤ middleAlpha ∧ middleAlpha ≤ (4/15:ℝ) ∧
    (79/100:ℝ) ≤ middleBeta ∧ middleBeta ≤ (4/5:ℝ) ∧
    0 ≤ middleRho ∧ middleRho ≤ (3/4:ℝ) := by
  have hlow : (229/50:ℝ) ≤ Real.sqrt 21 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hhigh : Real.sqrt 21 ≤ (23/5:ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hrlow : (1:ℝ) ≤ Real.sqrt 3 :=
    (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have hrhigh : Real.sqrt 3 ≤ (7/4:ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp only [middleAlpha, middleBeta, middleRho]
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

private lemma beta_one_alpha : middleBeta * (1 + middleAlpha) = 1 := by
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 21 by norm_num)
  dsimp only [middleAlpha, middleBeta]
  nlinarith

private lemma one_maps_interval (x : ℝ) (hx : x ∈ Set.Icc middleAlpha middleBeta) :
    prefixEval [1] x ∈ Set.Icc middleAlpha middleBeta := by
  obtain ⟨ha, ha', hb, hb', _, _⟩ := alpha_beta_bounds
  simp only [prefixEval, PNat.val_ofNat, Nat.cast_one]
  change middleAlpha ≤ 1 / (1+x) ∧ 1 / (1+x) ≤ middleBeta
  have hx0 : 0 < 1+x := by linarith [hx.1]
  constructor
  · apply (le_div_iff₀ hx0).2
    nlinarith [hx.2]
  · apply (div_le_iff₀ hx0).2
    have he := beta_one_alpha
    nlinarith [hx.1]

private lemma endpoint_tails :
    prefixEval [3] middleRho ∈ Set.Icc middleAlpha middleBeta ∧
    prefixEval [2] middleBeta ∈ Set.Icc middleAlpha middleBeta ∧
    prefixEval [1,3] middleRho ∈ Set.Icc middleAlpha middleBeta ∧
    prefixEval [1,2] middleBeta ∈ Set.Icc middleAlpha middleBeta := by
  obtain ⟨ha, ha', hb, hb', hr, hr'⟩ := alpha_beta_bounds
  have h3 : prefixEval [3] middleRho ∈ Set.Icc middleAlpha middleBeta := by
    change middleAlpha ≤ 1/(3+middleRho) ∧ 1/(3+middleRho) ≤ middleBeta
    have hp : 0 < 3+middleRho := by linarith
    constructor
    · apply (le_div_iff₀ hp).2
      nlinarith
    · apply (div_le_iff₀ hp).2
      nlinarith
  have h2 : prefixEval [2] middleBeta ∈ Set.Icc middleAlpha middleBeta := by
    change middleAlpha ≤ 1/(2+middleBeta) ∧ 1/(2+middleBeta) ≤ middleBeta
    have hp : 0 < 2+middleBeta := by linarith
    constructor
    · apply (le_div_iff₀ hp).2
      nlinarith
    · apply (div_le_iff₀ hp).2
      nlinarith
  refine ⟨h3, h2, ?_, ?_⟩
  · exact one_maps_interval _ h3
  · exact one_maps_interval _ h2

private noncomputable def wordLo (w : List ℕ+) : ℝ :=
  min (prefixEval w middleAlpha) (prefixEval w middleBeta)
private noncomputable def wordHi (w : List ℕ+) : ℝ :=
  max (prefixEval w middleAlpha) (prefixEval w middleBeta)
private noncomputable def cylinderLo (c : MiddleCore) : ℝ :=
  4 + wordLo c.left + wordLo c.right
private noncomputable def cylinderHi (c : MiddleCore) : ℝ :=
  4 + wordHi c.left + wordHi c.right

private lemma pe_interval (w : List ℕ+) (x : ℝ) (hx : x ∈ Set.Icc middleAlpha middleBeta) :
    wordLo w ≤ prefixEval w x ∧ prefixEval w x ≤ wordHi w := by
  obtain ⟨ha, ha', hb, hb', _, _⟩ := alpha_beta_bounds
  have hx0 : 0 ≤ x := by linarith [hx.1]
  have hax := pe_order w middleAlpha x (by linarith) hx0 hx.1
  have hxb := pe_order w x middleBeta hx0 (by linarith) hx.2
  by_cases he : w.length % 2 = 0
  · exact ⟨(min_le_left _ _).trans (hax.1 he), (hxb.1 he).trans (le_max_right _ _)⟩
  · have ho : w.length % 2 = 1 := by omega
    exact ⟨(min_le_right _ _).trans (hxb.2 ho), (hax.2 ho).trans (le_max_left _ _)⟩

private lemma e3_cylinder (c : MiddleCore) :
    cylinderLo c ≤ middleE3 c ∧ middleE3 c ≤ cylinderHi c := by
  obtain ⟨h3, h2, _, _⟩ := endpoint_tails
  have hab : middleAlpha ≤ middleBeta := by
    obtain ⟨ha, ha', hb, _, _, _⟩ := alpha_beta_bounds
    linarith
  unfold middleE3
  split_ifs
  · rw [pe_append, pe_append]
    have hl := pe_interval c.left _ h3
    have hr := pe_interval c.right _ h2
    constructor <;> dsimp only [cylinderLo, cylinderHi] <;> linarith only [hl.1, hl.2, hr.1, hr.2]
  · rw [pe_append]
    have hl := pe_interval c.left middleAlpha ⟨le_rfl, hab⟩
    have hr := pe_interval c.right _ h3
    constructor <;> dsimp only [cylinderLo, cylinderHi] <;> linarith only [hl.1, hl.2, hr.1, hr.2]

private lemma e13_cylinder (c : MiddleCore) :
    cylinderLo c ≤ middleE13 c ∧ middleE13 c ≤ cylinderHi c := by
  obtain ⟨_, _, h13, h12⟩ := endpoint_tails
  have hab : middleAlpha ≤ middleBeta := by
    obtain ⟨ha, ha', hb, _, _, _⟩ := alpha_beta_bounds
    linarith
  unfold middleE13
  split_ifs
  · rw [pe_append, pe_append]
    have hl := pe_interval c.left _ h13
    have hr := pe_interval c.right _ h12
    constructor <;> dsimp only [cylinderLo, cylinderHi] <;> linarith only [hl.1, hl.2, hr.1, hr.2]
  · rw [pe_append]
    have hl := pe_interval c.left middleBeta ⟨hab, le_rfl⟩
    have hr := pe_interval c.right _ h13
    constructor <;> dsimp only [cylinderLo, cylinderHi] <;> linarith only [hl.1, hl.2, hr.1, hr.2]

private lemma cylinder_normalized (c : MiddleCore) :
    cylinderLo (middleNormalized c) = cylinderLo c ∧
      cylinderHi (middleNormalized c) = cylinderHi c := by
  unfold middleNormalized
  split_ifs
  · exact ⟨rfl, rfl⟩
  · constructor <;> dsimp only [cylinderLo, cylinderHi] <;> ring

private lemma equal_cylinder (c : MiddleCore) :
    (middleEqualBounds c).1 ∈ Set.Icc (cylinderLo c) (cylinderHi c) ∧
      (middleEqualBounds c).2 ∈ Set.Icc (cylinderLo c) (cylinderHi c) := by
  have h3 := e3_cylinder (middleNormalized c)
  have h13 := e13_cylinder (middleNormalized c)
  rw [(cylinder_normalized c).1, (cylinder_normalized c).2] at h3 h13
  unfold middleEqualBounds
  dsimp only
  split_ifs
  · exact ⟨h3, h13⟩
  · exact ⟨h13, h3⟩

private lemma append_one_word (w : List ℕ+) :
    wordLo w ≤ wordLo (w++[1]) ∧ wordHi (w++[1]) ≤ wordHi w := by
  have hab : middleAlpha ≤ middleBeta := by
    obtain ⟨ha, ha', hb, _, _, _⟩ := alpha_beta_bounds
    linarith
  have ha := pe_interval w _ (one_maps_interval middleAlpha ⟨le_rfl, hab⟩)
  have hb := pe_interval w _ (one_maps_interval middleBeta ⟨hab, le_rfl⟩)
  change wordLo w ≤ min (prefixEval (w++[1]) middleAlpha) (prefixEval (w++[1]) middleBeta) ∧
    max (prefixEval (w++[1]) middleAlpha) (prefixEval (w++[1]) middleBeta) ≤ wordHi w
  rw [pe_append, pe_append]
  exact ⟨le_min ha.1 hb.1, max_le ha.2 hb.2⟩

private lemma bounds_cylinder (c : MiddleCore) :
    (middleBounds c).1 ∈ Set.Icc (cylinderLo c) (cylinderHi c) ∧
      (middleBounds c).2 ∈ Set.Icc (cylinderLo c) (cylinderHi c) := by
  let d := middleNormalized c
  have hn := cylinder_normalized c
  have h01 := equal_cylinder (⟨d.left, d.right++[1]⟩ : MiddleCore)
  have h10 := equal_cylinder (⟨d.left++[1], d.right⟩ : MiddleCore)
  have hl := append_one_word d.left
  have hr := append_one_word d.right
  unfold middleBounds
  dsimp only
  rw [← hn.1, ← hn.2]
  split_ifs
  · exact equal_cylinder d
  · dsimp only [Set.mem_Icc, cylinderLo, cylinderHi] at h01 h10 ⊢
    constructor <;> constructor <;>
      linarith only [h01.1.1, h01.1.2, h01.2.1, h01.2.2, h10.1.1, h10.1.2,
        h10.2.1, h10.2.2, hl.1, hl.2, hr.1, hr.2]
  · dsimp only [Set.mem_Icc, cylinderLo, cylinderHi] at h01 h10 ⊢
    constructor <;> constructor <;>
      linarith only [h01.1.1, h01.1.2, h01.2.1, h01.2.2, h10.1.1, h10.1.2,
        h10.2.1, h10.2.2, hl.1, hl.2, hr.1, hr.2]

private lemma zeta_unit : middleZeta ∈ Set.Icc (0:ℝ) 1 := by
  have h3 : (3:ℝ) ≤ Real.sqrt 13 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  have h5 : Real.sqrt 13 ≤ (5:ℝ) := Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  dsimp [middleZeta]
  constructor <;> linarith

private lemma zeta_fixed : prefixEval [3] middleZeta = middleZeta := by
  have hz := zeta_unit.1
  have hsq : Real.sqrt (13:ℝ)^2 = 13 := Real.sq_sqrt (by norm_num)
  change 1/(3+middleZeta) = middleZeta
  apply (div_eq_iff (by linarith : 3+middleZeta ≠ 0)).2
  unfold middleZeta
  nlinarith

private lemma replicate_zeta (k : ℕ) : prefixEval (List.replicate k (3:ℕ+)) middleZeta = middleZeta := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change prefixEval [3] (prefixEval (List.replicate k (3:ℕ+)) middleZeta) = middleZeta
    rw [ih]
    exact zeta_fixed

private lemma prefix_error (w : List ℕ+) (k : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) 1) :
    |prefixEval (w++List.replicate k (3:ℕ+)) x - prefixEval w middleZeta| ≤
      1 / ((Nat.fib (k+1):ℝ)^2) := by
  have hf : prefixEval (w++List.replicate k (3:ℕ+)) middleZeta = prefixEval w middleZeta := by
    rw [pe_append, replicate_zeta]
  have h := prefixEval_cylinder_bound (w++List.replicate k (3:ℕ+)) x middleZeta hx zeta_unit
  rw [hf] at h
  have hF : 0 < (Nat.fib (k+1):ℝ) := by exact_mod_cast Nat.fib_pos.mpr (Nat.succ_pos k)
  have hFG : (Nat.fib (k+1):ℝ) ≤ Nat.fib ((w++List.replicate k (3:ℕ+)).length+1) := by
    exact_mod_cast Nat.fib_mono (show k+1 ≤ (w++List.replicate k (3:ℕ+)).length+1 by
      simp only [List.length_append, List.length_replicate]; omega)
  have hsq : (Nat.fib (k+1):ℝ)^2 ≤ (Nat.fib ((w++List.replicate k (3:ℕ+)).length+1):ℝ)^2 := by
    nlinarith only [hF, hFG]
  exact h.trans (one_div_le_one_div_of_le (sq_pos_of_pos hF) hsq)

private lemma enclosure_error (u v : List ℕ+) (k : ℕ) (z : ℝ)
    (hz : z ∈ Set.Icc
      (cylinderLo ⟨u++List.replicate k 3,v++List.replicate k 3⟩)
      (cylinderHi ⟨u++List.replicate k 3,v++List.replicate k 3⟩)) :
    |z - (4+prefixEval u middleZeta+prefixEval v middleZeta)| ≤
      2 / ((Nat.fib (k+1):ℝ)^2) := by
  obtain ⟨ha, ha', hb, hb', _, _⟩ := alpha_beta_bounds
  have hA : middleAlpha ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hB : middleBeta ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hua := abs_le.mp (prefix_error u k middleAlpha hA)
  have hub := abs_le.mp (prefix_error u k middleBeta hB)
  have hva := abs_le.mp (prefix_error v k middleAlpha hA)
  have hvb := abs_le.mp (prefix_error v k middleBeta hB)
  let E : ℝ := 1 / ((Nat.fib (k+1):ℝ)^2)
  have huLo : prefixEval u middleZeta-E ≤ wordLo (u++List.replicate k 3) :=
    le_min (by linarith only [hua.1]) (by linarith only [hub.1])
  have huHi : wordHi (u++List.replicate k 3) ≤ prefixEval u middleZeta+E :=
    max_le (by linarith only [hua.2]) (by linarith only [hub.2])
  have hvLo : prefixEval v middleZeta-E ≤ wordLo (v++List.replicate k 3) :=
    le_min (by linarith only [hva.1]) (by linarith only [hvb.1])
  have hvHi : wordHi (v++List.replicate k 3) ≤ prefixEval v middleZeta+E :=
    max_le (by linarith only [hva.2]) (by linarith only [hvb.2])
  have he : 2 / ((Nat.fib (k+1):ℝ)^2) = E+E := by dsimp [E]; ring
  rw [he]
  apply abs_le.mpr
  dsimp only [Set.mem_Icc, cylinderLo, cylinderHi] at hz
  constructor <;> linarith only [hz.1, hz.2, huLo, huHi, hvLo, hvHi]

private lemma center_normalized (c : MiddleCore) :
    4+prefixEval (middleNormalized c).left middleZeta+prefixEval (middleNormalized c).right middleZeta =
      middleLimitValue c := by
  unfold middleNormalized middleLimitValue
  split_ifs
  · rfl
  · dsimp only
    ring

end M8Sep10JEndpoint

open M8Sep10JEndpoint

theorem solution :
    ∀ c : MiddleCore,
      Filter.Tendsto (fun k : ℕ => (middleBounds (middleRepairJ c k)).1) Filter.atTop (nhds (middleLimitValue c)) ∧
      Filter.Tendsto (fun k : ℕ => (middleBounds (middleRepairJ c k)).2) Filter.atTop (nhds (middleLimitValue c)) := by
  intro c
  have herror (k : ℕ) :
      |(middleBounds (middleRepairJ c k)).1-middleLimitValue c| ≤ 2 / ((Nat.fib (k+1):ℝ)^2) ∧
      |(middleBounds (middleRepairJ c k)).2-middleLimitValue c| ≤ 2 / ((Nat.fib (k+1):ℝ)^2) := by
    let d : MiddleCore := ⟨(middleNormalized c).left++List.replicate k 3,
      (middleNormalized c).right++List.replicate k 3⟩
    have h := bounds_cylinder (middleNormalized d)
    rw [(cylinder_normalized d).1, (cylinder_normalized d).2] at h
    have h1 := enclosure_error (middleNormalized c).left (middleNormalized c).right k _ h.1
    have h2 := enclosure_error (middleNormalized c).left (middleNormalized c).right k _ h.2
    rw [center_normalized c] at h1 h2
    exact ⟨h1,h2⟩
  constructor
  · apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    exact squeeze_zero (fun _ => abs_nonneg _) (fun k => (herror k).1) cylinder_bound_tendsto
  · apply tendsto_iff_dist_tendsto_zero.mpr
    simp only [Real.dist_eq]
    exact squeeze_zero (fun _ => abs_nonneg _) (fun k => (herror k).2) cylinder_bound_tendsto

#print axioms solution
