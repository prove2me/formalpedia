-- Prove2me | solution 1 for DistLTLSynth.Char.lemma_6_16
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:22:39.224584+00:00
-- url     : https://prove2.me/submissions/d20a816b-5158-4343-8108-916c4a0f87a2

import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric

namespace DistLTLSynth.Char.Lemma616Aux
open DistLTLSynth.Char

def stepJ (a : ℕ) (g : CommGraph) : ℕ := 3 * a + if a % 2 = 0 then delta g else 2 - delta g

lemma delta_le (g : CommGraph) : delta g ≤ 2 := by cases g <;> simp [delta]

lemma stepJ_bounds (a : ℕ) (g : CommGraph) : 3 * a ≤ stepJ a g ∧ stepJ a g ≤ 3 * a + 2 := by
  have := delta_le g
  unfold stepJ; split <;> omega

lemma jIdx_append (h : List CommGraph) (g : CommGraph) :
    jIdx (h ++ [g]) = stepJ (jIdx h) g := by
  unfold jIdx stepJ; rw [List.foldl_append]; rfl

lemma pre_succ (w : ℕ → CommGraph) (r : ℕ) : pre w (r + 1) = pre w r ++ [w r] := by
  unfold pre; rw [List.ofFn_succ', List.concat_eq_append]; simp

lemma pre_length (w : ℕ → CommGraph) (r : ℕ) : (pre w r).length = r := by simp [pre]

/-- left endpoints -/
noncomputable def lo (w : ℕ → CommGraph) (r : ℕ) : ℝ := (jIdx (pre w r) : ℝ) / 3 ^ r

lemma lo_mono (w : ℕ → CommGraph) : Monotone (lo w) := by
  apply monotone_nat_of_le_succ
  intro r
  have hb := stepJ_bounds (jIdx (pre w r)) (w r)
  unfold lo
  rw [pre_succ, jIdx_append]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : (3 * (jIdx (pre w r)) : ℝ) ≤ (stepJ (jIdx (pre w r)) (w r) : ℝ) := by exact_mod_cast hb.1
  rw [pow_succ]; nlinarith [pow_pos (show (0:ℝ) < 3 by norm_num) r]

lemma hi_anti (w : ℕ → CommGraph) : Antitone (fun r => lo w r + 1 / 3 ^ r) := by
  apply antitone_nat_of_succ_le
  intro r
  have hb := stepJ_bounds (jIdx (pre w r)) (w r)
  unfold lo
  rw [pre_succ, jIdx_append]
  have h3 : (stepJ (jIdx (pre w r)) (w r) : ℝ) ≤ 3 * (jIdx (pre w r)) + 2 := by exact_mod_cast hb.2
  have hp : (0:ℝ) < 3 ^ r := by positivity
  have e1 : (stepJ (jIdx (pre w r)) (w r) : ℝ) / 3 ^ (r + 1) + 1 / 3 ^ (r + 1)
      = ((stepJ (jIdx (pre w r)) (w r) : ℝ) + 1) / (3 * 3 ^ r) := by rw [pow_succ]; ring
  have e2 : (jIdx (pre w r) : ℝ) / 3 ^ r + 1 / 3 ^ r = ((jIdx (pre w r) : ℝ) + 1) / 3 ^ r := by
    ring
  rw [e1, e2, div_le_div_iff₀ (by positivity) hp]
  nlinarith

lemma lo_le_hi (w : ℕ → CommGraph) (s r : ℕ) : lo w s ≤ lo w r + 1 / 3 ^ r := by
  rcases le_total s r with h | h
  · have := lo_mono w h; have : (0:ℝ) ≤ 1 / 3 ^ r := by positivity
    linarith
  · have := hi_anti w h; have : (0:ℝ) < 1 / 3 ^ s := by positivity
    linarith

lemma bdd (w : ℕ → CommGraph) : BddAbove (Set.range (lo w)) :=
  ⟨lo w 0 + 1 / 3 ^ 0, by rintro _ ⟨s, rfl⟩; exact lo_le_hi w s 0⟩

lemma piMap_mem (w : ℕ → CommGraph) (r : ℕ) : lo w r ≤ piMap w ∧ piMap w ≤ lo w r + 1 / 3 ^ r :=
  ⟨le_ciSup (bdd w) r, ciSup_le (fun s => lo_le_hi w s r)⟩

lemma lo_zero (w : ℕ → CommGraph) : lo w 0 = 0 := by simp [lo, pre, jIdx]

lemma lo_nonneg (w : ℕ → CommGraph) (r : ℕ) : 0 ≤ lo w r := by unfold lo; positivity

lemma piMap_close (w w' : ℕ → CommGraph) (r : ℕ) (h : pre w r = pre w' r) :
    |piMap w - piMap w'| ≤ 1 / 3 ^ r := by
  have h1 := piMap_mem w r; have h2 := piMap_mem w' r
  have : lo w r = lo w' r := by simp [lo, h]
  rw [abs_le]; constructor <;> linarith

lemma jIdx_surj : ∀ (r k : ℕ), k < 3 ^ r → ∃ h : List CommGraph, h.length = r ∧ jIdx h = k
  | 0, k, hk => ⟨[], rfl, by simp [jIdx] at hk ⊢; omega⟩
  | r + 1, k, hk => by
      obtain ⟨h, hl, hj⟩ := jIdx_surj r (k / 3) (by rw [pow_succ] at hk; omega)
      have hd : ∀ d, d ≤ 2 → ∃ g, delta g = d := by
        intro d hd
        rcases (show d = 0 ∨ d = 1 ∨ d = 2 by omega) with rfl | rfl | rfl
        · exact ⟨.oneToTwo, rfl⟩
        · exact ⟨.both, rfl⟩
        · exact ⟨.twoToOne, rfl⟩
      by_cases he : (k / 3) % 2 = 0
      · obtain ⟨g, hg⟩ := hd (k % 3) (by omega)
        refine ⟨h ++ [g], by simp [hl], ?_⟩
        rw [jIdx_append, hj]; simp [stepJ, he, hg]; omega
      · obtain ⟨g, hg⟩ := hd (2 - k % 3) (by omega)
        refine ⟨h ++ [g], by simp [hl], ?_⟩
        rw [jIdx_append, hj]; simp [stepJ, he, hg]; omega

lemma extend (h : List CommGraph) : ∃ w : ℕ → CommGraph, pre w h.length = h := by
  refine ⟨fun i => h.getD i .both, ?_⟩
  apply List.ext_getElem
  · simp [pre]
  · intro i h1 h2; simp [pre]


lemma hpow : ∀ ε : ℝ, 0 < ε → ∃ r : ℕ, 1 / (3:ℝ) ^ r < ε := by
  intro ε hε
  obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (show (1:ℝ) / 3 < 1 by norm_num)
  exact ⟨r, by simpa [div_pow] using hr⟩

noncomputable def Lv (g : List CommGraph) : ℝ := (jIdx g : ℝ) / 3 ^ g.length

lemma lo_eq (w : ℕ → CommGraph) (r : ℕ) : lo w r = Lv (pre w r) := by
  simp [lo, Lv, pre_length]

lemma pre_take (w : ℕ → CommGraph) (n m : ℕ) (h : n ≤ m) : pre w n = (pre w m).take n := by
  apply List.ext_getElem
  · simp [pre]; omega
  · intro i h1 h2; simp [pre]

lemma nest (g : List CommGraph) (n : ℕ) (hn : n ≤ g.length) :
    Lv (g.take n) ≤ Lv g ∧ Lv g + 1 / 3 ^ g.length ≤ Lv (g.take n) + 1 / 3 ^ n := by
  obtain ⟨w, hw⟩ := extend g
  have ht : g.take n = pre w n := by rw [pre_take w n g.length hn, hw]
  have h1 := lo_mono w hn
  have h2 := hi_anti w hn
  simp only [lo_eq, ht, hw] at h1 h2 ⊢
  exact ⟨h1, h2⟩

lemma delta_inj {x y : CommGraph} (h : delta x = delta y) : x = y := by
  cases x <;> cases y <;> simp_all [delta]

lemma inj_pre : ∀ (m : ℕ) (w w' : ℕ → CommGraph),
    jIdx (pre w m) = jIdx (pre w' m) → pre w m = pre w' m
  | 0, w, w', _ => by simp [pre]
  | m + 1, w, w', h => by
      rw [pre_succ, pre_succ] at h ⊢
      rw [jIdx_append, jIdx_append] at h
      have b1 := stepJ_bounds (jIdx (pre w m)) (w m)
      have b2 := stepJ_bounds (jIdx (pre w' m)) (w' m)
      have ha : jIdx (pre w m) = jIdx (pre w' m) := by omega
      have hp := inj_pre m w w' ha
      rw [hp]; congr 2
      rw [ha] at h
      apply delta_inj
      have d1 := delta_le (w m); have d2 := delta_le (w' m)
      unfold stepJ at h
      split at h <;> omega

lemma inj_list (g g' : List CommGraph) (hl : g.length = g'.length) (h : jIdx g = jIdx g') :
    g = g' := by
  obtain ⟨w, hw⟩ := extend g
  obtain ⟨w', hw'⟩ := extend g'
  rw [← hl] at hw'
  rw [← hw, ← hw'] at h ⊢
  exact inj_pre _ w w' h

lemma find (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) (r : ℕ) :
    ∃ g : List CommGraph, g.length = r ∧ Lv g ≤ t ∧ t ≤ Lv g + 1 / 3 ^ r := by
  have hp : (0:ℝ) < 3 ^ r := by positivity
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = min ⌊t * 3 ^ r⌋₊ (3 ^ r - 1) := ⟨_, rfl⟩
  have hk3 : k < 3 ^ r := by
    have : 0 < 3 ^ r := by positivity
    omega
  have hkt : (k : ℝ) / 3 ^ r ≤ t := by
    rw [div_le_iff₀ hp]
    have : (k : ℝ) ≤ ⌊t * 3 ^ r⌋₊ := by rw [hk]; exact_mod_cast min_le_left _ _
    have := Nat.floor_le (show 0 ≤ t * 3 ^ r by nlinarith [ht.1])
    linarith
  have htk : t ≤ ((k : ℝ) + 1) / 3 ^ r := by
    rw [le_div_iff₀ hp]
    rcases le_total ⌊t * 3 ^ r⌋₊ (3 ^ r - 1) with h | h
    · have e : k = ⌊t * 3 ^ r⌋₊ := hk.trans (min_eq_left h)
      rw [e]; exact (Nat.lt_floor_add_one _).le
    · have e : k = 3 ^ r - 1 := hk.trans (min_eq_right h)
      have h1 : (1:ℕ) ≤ 3 ^ r := Nat.one_le_pow _ _ (by norm_num)
      have : ((3 ^ r - 1 : ℕ) : ℝ) = (3:ℝ) ^ r - 1 := by
        rw [Nat.cast_sub h1]; simp
      rw [e, this]; nlinarith [ht.2]
  obtain ⟨g, hl, hj⟩ := jIdx_surj r k hk3
  refine ⟨g, hl, ?_, ?_⟩
  · simp [Lv, hl, hj, hkt]
  · simp only [Lv, hl, hj]
    have : ((k : ℝ) + 1) / 3 ^ r = (k : ℝ) / 3 ^ r + 1 / 3 ^ r := by ring
    linarith

lemma idx_eq (a b m : ℕ) (t : ℝ)
    (h1 : (a : ℝ) / 3 ^ m ≤ t) (h2 : t ≤ (a : ℝ) / 3 ^ m + 1 / 3 ^ m)
    (h3 : (b : ℝ) / 3 ^ m < t) (h4 : t < (b : ℝ) / 3 ^ m + 1 / 3 ^ m) : a = b := by
  have hp : (0:ℝ) < 3 ^ m := by positivity
  have e1 : (a : ℝ) / 3 ^ m + 1 / 3 ^ m = ((a : ℝ) + 1) / 3 ^ m := by ring
  have e2 : (b : ℝ) / 3 ^ m + 1 / 3 ^ m = ((b : ℝ) + 1) / 3 ^ m := by ring
  rw [e1] at h2; rw [e2] at h4
  rw [div_le_iff₀ hp] at h1; rw [le_div_iff₀ hp] at h2
  rw [div_lt_iff₀ hp] at h3; rw [lt_div_iff₀ hp] at h4
  have hab : (a : ℝ) < b + 1 := by linarith
  have hba : (b : ℝ) < a + 1 := by linarith
  have : a < b + 1 := by exact_mod_cast hab
  have : b < a + 1 := by exact_mod_cast hba
  omega

lemma range_sub (A : Set (ℕ → CommGraph)) : piMap '' A ⊆ Set.Icc (0:ℝ) 1 := by
  rintro _ ⟨w, -, rfl⟩
  have h0 := piMap_mem w 0
  rw [lo_zero] at h0
  exact ⟨h0.1, by simpa using h0.2⟩

lemma piMap_mem' (w : ℕ → CommGraph) (r : ℕ) :
    Lv (pre w r) ≤ piMap w ∧ piMap w ≤ Lv (pre w r) + 1 / 3 ^ r := by
  rw [← lo_eq]; exact piMap_mem w r

end DistLTLSynth.Char.Lemma616Aux

namespace DistLTLSynth.Char.Lemma616Aux
open DistLTLSynth.Char
theorem nd_iff (A : Set (ℕ → CommGraph)) :
    IsNowhereDense (piMap '' A) ↔
      ∀ h : List CommGraph, ∃ k : List CommGraph, h ++ k ∉ Pref A := by
  constructor
  · intro hND h
    by_contra hc
    push_neg at hc
    set n := h.length
    -- the open interval of `h` lies in the closure
    have hO : Set.Ioo (Lv h) (Lv h + 1 / 3 ^ n) ⊆ closure (piMap '' A) := by
      intro t ht
      have ht01 : t ∈ Set.Icc (0:ℝ) 1 := by
        have h0 : 0 ≤ Lv h := by unfold Lv; positivity
        have := (nest h 0 (Nat.zero_le _)).2
        have hz : Lv (h.take 0) = 0 := by simp [Lv, jIdx]
        rw [hz] at this
        have h3 : Lv h + 1 / 3 ^ h.length ≤ 1 := by simpa using this
        have h2 : t < Lv h + 1 / 3 ^ h.length := ht.2
        exact ⟨by linarith [ht.1], by linarith⟩
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨r', hr'⟩ := hpow ε hε
      obtain ⟨g, hgl, hg1, hg2⟩ := find t ht01 (r' + n)
      have hnl : n ≤ g.length := by omega
      have hN := nest g n hnl
      rw [hgl] at hN
      have e : g.take n = h := by
        apply inj_list _ _ (by simp; omega)
        have hLt : Lv (g.take n) = (jIdx (g.take n) : ℝ) / 3 ^ n := by
          rw [Lv, List.length_take, min_eq_left hnl]
        have hLh : Lv h = (jIdx h : ℝ) / 3 ^ n := rfl
        apply idx_eq _ _ n t
        · rw [← hLt]; linarith [hN.1, hg1]
        · rw [← hLt]; linarith [hN.2, hg2]
        · rw [← hLh]; exact ht.1
        · rw [← hLh]; exact ht.2
      have hg : g = h ++ g.drop n := by
        conv_lhs => rw [← List.take_append_drop n g]
        rw [e]
      obtain ⟨w, hwA, hw⟩ := hc (g.drop n)
      rw [← hg] at hw
      refine ⟨piMap w, ⟨w, hwA, rfl⟩, ?_⟩
      have hm := piMap_mem' w g.length
      rw [hw, hgl] at hm
      have hle : 1 / (3:ℝ) ^ (r' + n) ≤ 1 / 3 ^ r' := by
        apply one_div_le_one_div_of_le (by positivity)
        exact pow_le_pow_right₀ (by norm_num) (by omega)
      rw [Real.dist_eq, abs_lt]; constructor <;> linarith
    have hsub : Set.Ioo (Lv h) (Lv h + 1 / 3 ^ n) ⊆ interior (closure (piMap '' A)) :=
      interior_maximal hO isOpen_Ioo
    rw [hND] at hsub
    have hpos : (0:ℝ) < 1 / 3 ^ n := by positivity
    exact hsub (a := Lv h + 1 / 3 ^ n / 2) ⟨by linarith, by linarith⟩
  · intro hk
    by_contra hND
    have hne : (interior (closure (piMap '' A))).Nonempty :=
      Set.nonempty_iff_ne_empty.2 hND
    obtain ⟨t, ht⟩ := hne
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 isOpen_interior t ht
    have htc : t ∈ closure (piMap '' A) := interior_subset ht
    have ht01 : t ∈ Set.Icc (0:ℝ) 1 :=
      closure_minimal (range_sub A) isClosed_Icc htc
    obtain ⟨r, hr⟩ := hpow (ε / 2) (by linarith)
    obtain ⟨h, hl, hh1, hh2⟩ := find t ht01 r
    obtain ⟨k, hkA⟩ := hk h
    set g := h ++ k
    set m := g.length
    have hrm : r ≤ m := by simp [g, m, hl]
    have hN := nest g r hrm
    have htk : g.take r = h := by simp [g, ← hl]
    rw [htk] at hN
    change Lv h ≤ Lv g ∧ Lv g + 1 / 3 ^ m ≤ Lv h + 1 / 3 ^ r at hN
    set δ := 1 / (3:ℝ) ^ m / 2
    have hδ : 0 < δ := by positivity
    set c := Lv g + δ
    have hcl : c ∈ closure (piMap '' A) := by
      apply interior_subset
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      have : δ ≤ 1 / 3 ^ m := by simp only [δ]; linarith [show (0:ℝ) < 1 / 3 ^ m by positivity]
      constructor <;> linarith [hN.1, hN.2]
    obtain ⟨b, ⟨w, hwA, rfl⟩, hb⟩ := Metric.mem_closure_iff.1 hcl δ hδ
    rw [Real.dist_eq, abs_lt] at hb
    have hm := piMap_mem' w m
    have heq : jIdx (pre w m) = jIdx g := by
      apply idx_eq _ _ m (piMap w)
      · have := hm.1; unfold Lv at this; rw [pre_length] at this; exact this
      · have := hm.2; unfold Lv at this; rw [pre_length] at this; exact this
      · have : Lv g < piMap w := by linarith [hb.1, hb.2]
        unfold Lv at this; exact this
      · have : piMap w < Lv g + 1 / 3 ^ m := by
          have : δ * 2 = 1 / 3 ^ m := by simp only [δ]; ring
          linarith [hb.1, hb.2]
        unfold Lv at this; exact this
    have hpg : pre w m = g := inj_list _ _ (by rw [pre_length]) heq
    exact hkA ⟨w, hwA, hpg⟩

lemma pre_eq_iff (w v : ℕ → CommGraph) (r : ℕ) : pre w r = pre v r ↔ ∀ i < r, w i = v i := by
  constructor
  · intro h i hi
    have := congrArg (fun l => l[i]?) h
    simpa [pre, hi] using this
  · intro h; simp only [pre]; congr 1; funext i; exact h i i.2

end DistLTLSynth.Char.Lemma616Aux

open DistLTLSynth.Char DistLTLSynth.Char.Lemma616Aux in
theorem solution (A : Set (ℕ → CommGraph)) (hA : ¬ IsNowhereDense (piMap '' A)) :
    ∃ h : List CommGraph, Dense (leftQuot h A) := by
  rw [nd_iff] at hA
  push_neg at hA
  obtain ⟨h, hh⟩ := hA
  refine ⟨h, ?_⟩
  rw [dense_iff_inter_open]
  rintro U hU ⟨v0, hv0⟩
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hU v0 hv0
  set r := I.sup id + 1
  obtain ⟨w, hwA, hw⟩ := hh (pre v0 r)
  have hlen : (h ++ pre v0 r).length = h.length + r := by simp [pre_length]
  rw [hlen] at hw
  refine ⟨fun i => w (h.length + i), ?_, ?_⟩
  · apply hsub
    intro a ha
    have har : a < r := Nat.lt_succ_of_le (Finset.le_sup (f := id) ha)
    have := congrArg (fun l => l[h.length + a]?) hw
    simp only [pre, List.getElem?_ofFn] at this
    have h2 : h.length + a < h.length + r := by omega
    simp only [h2, dite_true, Option.some.injEq] at this
    rw [List.getElem?_append_right (by omega)] at this
    simp only [Nat.add_sub_cancel_left, List.getElem?_ofFn, har, dite_true,
      Option.some.injEq] at this
    show w (h.length + a) ∈ u a
    rw [this]; exact (hu a ha).2
  · show append h (fun i => w (h.length + i)) ∈ A
    convert hwA using 1
    funext n
    unfold append
    split_ifs with hn
    · have := congrArg (fun l => l[n]?) hw
      simp only [pre, List.getElem?_ofFn] at this
      have h2 : n < h.length + r := by omega
      simp only [h2, dite_true] at this
      rw [List.getElem?_append_left hn] at this
      simp only [List.getElem?_eq_getElem hn, Option.some.injEq] at this
      exact this.symm
    · show w (h.length + (n - h.length)) = w n
      rw [Nat.add_sub_cancel' (by omega)]
