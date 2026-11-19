-- Prove2me | solution 1 for DistLTLSynth.Char.lemma_2_4
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-18T16:19:10.578185+00:00
-- url     : https://prove2.me/submissions/5eed8d2e-5960-49dc-8717-36f72ecc7084

import Definitions.Def_DistLTLSynth_Char_Model
import Definitions.Def_DistLTLSynth_Char_Geometric

namespace DistLTLSynth.Char.Lemma24Aux
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
  · intro i h1 h2; simp [pre, List.getD_eq_getElem _ _ h2]

end DistLTLSynth.Char.Lemma24Aux

open DistLTLSynth.Char DistLTLSynth.Char.Lemma24Aux in
theorem solution : Continuous piMap ∧ Set.range piMap = Set.Icc (0 : ℝ) 1 := by
  have hpow : ∀ ε : ℝ, 0 < ε → ∃ r : ℕ, 1 / (3:ℝ) ^ r < ε := by
    intro ε hε
    obtain ⟨r, hr⟩ := exists_pow_lt_of_lt_one hε (show (1:ℝ) / 3 < 1 by norm_num)
    exact ⟨r, by simpa [div_pow] using hr⟩
  have key : ∀ (w : ℕ → CommGraph) (r : ℕ), ∀ᶠ w' in nhds w, pre w' r = pre w r := by
    intro w r
    have : ∀ i : Fin r, ∀ᶠ w' in nhds w, w' i = w i := by
      intro i
      exact ((continuous_apply (i : ℕ)).tendsto w).eventually
        ((isOpen_discrete {w i}).mem_nhds rfl)
    rw [← Filter.eventually_all] at this
    filter_upwards [this] with w' hw'
    simp [pre, hw']
  have hcont : Continuous piMap := by
    rw [continuous_iff_continuousAt]
    intro w
    rw [ContinuousAt, Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨r, hr⟩ := hpow ε hε
    filter_upwards [key w r] with w' hw'
    rw [Real.dist_eq]
    exact lt_of_le_of_lt (piMap_close w' w r hw') hr
  refine ⟨hcont, ?_⟩
  apply Set.Subset.antisymm
  · rintro _ ⟨w, rfl⟩
    have h0 := piMap_mem w 0
    rw [lo_zero] at h0
    exact ⟨h0.1, by simpa using h0.2⟩
  · have hcl : IsClosed (Set.range piMap) := (isCompact_range hcont).isClosed
    intro t ht
    rw [← hcl.closure_eq, Metric.mem_closure_iff]
    intro ε hε
    obtain ⟨r, hr⟩ := hpow ε hε
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
    obtain ⟨h, hl, hj⟩ := jIdx_surj r k hk3
    obtain ⟨w, hw⟩ := extend h
    rw [hl] at hw
    refine ⟨piMap w, ⟨w, rfl⟩, ?_⟩
    have hm := piMap_mem w r
    have hlo : lo w r = (k : ℝ) / 3 ^ r := by simp [lo, hw, hj]
    rw [hlo] at hm
    rw [Real.dist_eq, abs_lt]
    have : ((k : ℝ) + 1) / 3 ^ r = (k : ℝ) / 3 ^ r + 1 / 3 ^ r := by ring
    constructor <;> linarith
