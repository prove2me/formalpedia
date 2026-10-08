-- Prove2me | solution 1 for DantzigSimplex.Technique.simplex_technique_terminates
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T13:42:05.020135+00:00
-- url     : https://prove2.me/submissions/e04f85d9-f6e7-4e60-aed4-c8c285abcf3c

import Mathlib
import Definitions.Def_DantzigSimplex_Technique_Process



namespace DantzigSimplex.Technique

def Ind {m : ℕ} {κ : Type*} (v : κ → (Fin m → ℝ)) (T : Finset κ) : Prop :=
  LinearIndependent ℝ (fun a : {j // j ∈ T} => v a.1)

section Generic
variable {m : ℕ} {κ : Type*} [DecidableEq κ] (v : κ → (Fin m → ℝ))

lemma ind_iff {T : Finset κ} : Ind v T ↔
    ∀ g : κ → ℝ, ∑ i ∈ T, g i • v i = 0 → ∀ i ∈ T, g i = 0 := by
  unfold Ind
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h g hg i hi
    have h2 : ∑ a : {j // j ∈ T}, (fun a : {j // j ∈ T} => g a.1) a • v a.1 = 0 := by
      rw [Finset.sum_coe_sort T (fun i => g i • v i)]; exact hg
    exact h _ h2 ⟨i, hi⟩
  · intro h g hg a
    let g' : κ → ℝ := fun i => if hi : i ∈ T then g ⟨i, hi⟩ else 0
    have h1 : ∑ i ∈ T, g' i • v i = 0 := by
      rw [← Finset.sum_coe_sort T (fun i => g' i • v i)]
      rw [← hg]; apply Finset.sum_congr rfl; intro x _; simp [g', x.2]
    have := h g' h1 a.1 a.2
    simpa [g', a.2] using this

lemma ind_span {T : Finset κ} (hT : Ind v T) (hc : T.card = m) (u : Fin m → ℝ) :
    ∃ c : κ → ℝ, u = ∑ i ∈ T, c i • v i := by
  have hcard : Fintype.card {j // j ∈ T} = Module.finrank ℝ (Fin m → ℝ) := by simp [hc]
  have h := LinearIndependent.span_eq_top_of_card_eq_finrank' hT hcard
  have hu : u ∈ Submodule.span ℝ (Set.range (fun a : {j // j ∈ T} => v a.1)) := by
    rw [h]; trivial
  rw [Submodule.mem_span_range_iff_exists_fun] at hu
  obtain ⟨c, hc'⟩ := hu
  refine ⟨fun i => if hi : i ∈ T then c ⟨i, hi⟩ else 0, ?_⟩
  rw [← hc', ← Finset.sum_coe_sort T (fun i => (if hi : i ∈ T then c ⟨i, hi⟩ else 0) • v i)]
  apply Finset.sum_congr rfl; intro x _; simp [x.2]

lemma ind_of_span {T : Finset κ} (hc : T.card = m)
    (h : ∀ u : Fin m → ℝ, ∃ c : κ → ℝ, u = ∑ i ∈ T, c i • v i) : Ind v T := by
  unfold Ind
  apply linearIndependent_of_top_le_span_of_card_eq_finrank
  · intro u _
    obtain ⟨c, hc'⟩ := h u
    rw [hc', ← Finset.sum_coe_sort T (fun i => c i • v i)]
    apply Submodule.sum_mem; intro i _
    apply Submodule.smul_mem
    exact Submodule.subset_span ⟨i, rfl⟩
  · simp [hc]

lemma ind_uniq {T : Finset κ} (hT : Ind v T) {c d : κ → ℝ}
    (h : ∑ i ∈ T, c i • v i = ∑ i ∈ T, d i • v i) : ∀ i ∈ T, c i = d i := by
  have := (ind_iff v).1 hT (fun i => c i - d i)
    (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self])
  intro i hi; have := this i hi; linarith

lemma exch_sum {T : Finset κ} {j i₀ : κ} (hj : j ∉ T) (hi : i₀ ∈ T) {c d : κ → ℝ}
    (hc0 : c i₀ ≠ 0) (hc : v j = ∑ i ∈ T, c i • v i) :
    ∑ i ∈ T, d i • v i = ∑ i ∈ insert j (T.erase i₀),
      (if i = j then d i₀ / c i₀ else d i - d i₀ / c i₀ * c i) • v i := by
  have hjn : j ∉ T.erase i₀ := fun h => hj (Finset.mem_of_mem_erase h)
  rw [Finset.sum_insert hjn]
  have e1 : ∀ i ∈ T.erase i₀, (if i = j then d i₀ / c i₀ else d i - d i₀ / c i₀ * c i) • v i
      = d i • v i - (d i₀ / c i₀) • (c i • v i) := by
    intro i hi
    have : i ≠ j := fun h => hjn (h ▸ hi)
    simp [this, sub_smul, mul_smul]
  rw [Finset.sum_congr rfl e1, Finset.sum_sub_distrib, ← Finset.smul_sum]
  simp only [if_true]
  rw [hc]
  rw [← Finset.add_sum_erase T (fun i => c i • v i) hi, ← Finset.add_sum_erase T (fun i => d i • v i) hi]
  have : d i₀ / c i₀ * c i₀ = d i₀ := by field_simp
  rw [smul_add, ← mul_smul, this]
  abel

lemma pivot_ind {T : Finset κ} (hT : Ind v T) (hcard : T.card = m) {j i₀ : κ}
    (hj : j ∉ T) (hi : i₀ ∈ T) {c : κ → ℝ} (hc0 : c i₀ ≠ 0)
    (hc : v j = ∑ i ∈ T, c i • v i) : Ind v (insert j (T.erase i₀)) := by
  have hjn : j ∉ T.erase i₀ := fun h => hj (Finset.mem_of_mem_erase h)
  apply ind_of_span
  · rw [Finset.card_insert_of_notMem hjn, Finset.card_erase_of_mem hi]
    have : 0 < T.card := Finset.card_pos.2 ⟨i₀, hi⟩
    omega
  · intro u
    obtain ⟨d, hd⟩ := ind_span v hT hcard u
    exact ⟨_, by rw [hd]; exact exch_sum v hj hi hc0 hc⟩

end Generic


section PII
variable {m n : ℕ} (p : Problem m n)

lemma combine_eq (w : Fin n → ℝ) : p.combine w = ∑ j, w j • p.col j := by
  funext a; simp [Problem.combine, Finset.sum_apply]

lemma sum_opt (g : Option (Fin n) → ℝ) (R : Finset (Fin n)) :
    ∑ a ∈ insert none (R.image some), g a • p.point a
      = g none • p.rhs + ∑ k ∈ R, g (some k) • p.col k := by
  rw [Finset.sum_insert (by simp), Finset.sum_image (fun a _ b _ h => Option.some_injective _ h)]
  rfl

omit p in
lemma sum_piece {M : Type*} [AddCommMonoid M] {S : Finset (Fin n)} {j : Fin n} (hj : j ∉ S)
    (F : Fin n → ℝ → M) (hF : ∀ k, F k 0 = 0) (a : ℝ) (b : Fin n → ℝ) :
    ∑ k, F k (if k = j then a else if k ∈ S then b k else 0) = F j a + ∑ k ∈ S, F k (b k) := by
  calc ∑ k, F k (if k = j then a else if k ∈ S then b k else 0)
      = ∑ k ∈ insert j S, F k (if k = j then a else if k ∈ S then b k else 0) :=
        (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by
          have h1 : k ≠ j := fun h => hk (by simp [h])
          have h2 : k ∉ S := fun h => hk (by simp [h])
          simp [h1, h2, hF])).symm
    _ = F j a + ∑ k ∈ S, F k (b k) := by
        rw [Finset.sum_insert hj]
        simp only [if_true]
        congr 1
        apply Finset.sum_congr rfl; intro k hk
        have : k ≠ j := fun h => hj (h ▸ hk)
        simp [this, hk]

lemma II_coord (q : PhaseIIFrame p) (j : Fin n) : ∑ i ∈ q.B, q.x i j • p.col i = p.col j := by
  funext a; have := congrFun (q.hcoord j) a; simpa [Finset.sum_apply] using this

lemma II_z_mem (q : PhaseIIFrame p) {j : Fin n} (hj : j ∈ q.B) : q.z j = p.cost j := by
  have h := ind_uniq p.col q.hind (c := fun i => q.x i j) (d := fun i => if i = j then 1 else 0)
    (by rw [II_coord]; simp [ite_smul, hj])
  unfold PhaseIIFrame.z
  rw [Finset.sum_congr rfl (fun i hi => by rw [h i hi])]
  simp [hj]

lemma II_weight_sum (s : PhaseIIState p) : ∑ i ∈ s.frame.B, s.weight i • p.col i = p.rhs := by
  have h := s.hfeasible.2
  rw [combine_eq] at h
  rw [← h]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk; simp [s.hzero k hk]

lemma II_obj (s : PhaseIIState p) :
    p.objective s.weight = ∑ i ∈ s.frame.B, s.weight i * p.cost i := by
  unfold Problem.objective
  symm; apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk; simp [s.hzero k hk]

lemma II_obj_new (s : PhaseIIState p) {j : Fin n} (hj : j ∉ s.frame.B) (θ : ℝ) :
    p.objective (phaseIIWeights s j θ)
      = p.objective s.weight + θ * (p.cost j - s.frame.z j) := by
  have := sum_piece (S := s.frame.B) hj (fun k r => r * p.cost k) (by simp) θ
    (fun k => s.weight k - θ * s.frame.x k j)
  beta_reduce at this
  unfold Problem.objective at *
  simp only [phaseIIWeights]
  rw [this]
  have h2 := II_obj p s
  unfold Problem.objective at h2
  rw [h2]
  unfold PhaseIIFrame.z
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  ring

lemma II_comb_new (s : PhaseIIState p) {j : Fin n} (hj : j ∉ s.frame.B) (θ : ℝ) :
    p.combine (phaseIIWeights s j θ) = p.rhs := by
  rw [combine_eq]
  have := sum_piece (S := s.frame.B) hj (fun k r => r • p.col k) (by simp) θ
    (fun k => s.weight k - θ * s.frame.x k j)
  beta_reduce at this
  simp only [phaseIIWeights]
  rw [this]
  simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, II_weight_sum,
    II_coord]
  abel

lemma II_notin (s : PhaseIIState p) {j : Fin n} (hj : p.cost j > s.frame.z j) :
    j ∉ s.frame.B := fun h => by rw [II_z_mem p s.frame h] at hj; exact lt_irrefl _ hj

lemma II_step_obj {s t : PhaseIIState p} (h : PhaseIIStep s t) :
    p.objective s.weight < p.objective t.weight := by
  obtain ⟨j, i₀, θ, hjB, hi₀, hcost, hx, hθ, hmin, hB, hw⟩ := h
  have hθpos : 0 < θ := by rw [hθ]; exact div_pos (s.hpositive i₀ hi₀) hx
  rw [hw, II_obj_new p s hjB]
  have : 0 < θ * (p.cost j - s.frame.z j) := mul_pos hθpos (by linarith)
  linarith


lemma II_w'_mem (s : PhaseIIState p) {j : Fin n} (hj : j ∉ s.frame.B) (θ : ℝ) {k : Fin n}
    (hk : k ∈ s.frame.B) : phaseIIWeights s j θ k = s.weight k - θ * s.frame.x k j := by
  have : k ≠ j := fun h => hj (h ▸ hk)
  simp [phaseIIWeights, this, hk]

lemma II_tie (hnd : p.Nondegenerate) (s : PhaseIIState p) {j i₀ i : Fin n} {θ : ℝ}
    (hj : j ∉ s.frame.B) (hi₀ : i₀ ∈ s.frame.B) (hi : i ∈ s.frame.B.erase i₀)
    (h0i₀ : s.weight i₀ - θ * s.frame.x i₀ j = 0)
    (h0 : s.weight i - θ * s.frame.x i j = 0) : False := by
  have hiB : i ∈ s.frame.B := Finset.mem_of_mem_erase hi
  have hii : i ≠ i₀ := Finset.ne_of_mem_erase hi
  have hjR : j ∉ (s.frame.B.erase i₀).erase i := fun h =>
    hj (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hsupp : ∀ k, k ∉ insert j ((s.frame.B.erase i₀).erase i) → phaseIIWeights s j θ k = 0 := by
    intro k hk
    by_cases hkB : k ∈ s.frame.B
    · rw [II_w'_mem p s hj θ hkB]
      by_cases h1 : k = i₀
      · rw [h1]; exact h0i₀
      · by_cases h2 : k = i
        · rw [h2]; exact h0
        · exfalso; apply hk
          by_cases h3 : k = j
          · simp [h3]
          · simp [h1, h2, hkB]
    · have : k ≠ j := fun h => hk (by simp [h])
      simp [phaseIIWeights, this, hkB]
  have hrhs : p.rhs = ∑ k ∈ insert j ((s.frame.B.erase i₀).erase i),
      phaseIIWeights s j θ k • p.col k := by
    rw [← II_comb_new p s hj θ, combine_eq]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by simp [hsupp k hk])).symm
  have hc1 : (s.frame.B.erase i₀).card = m - 1 := by
    rw [Finset.card_erase_of_mem hi₀, s.frame.hcard]
  have hc2 : ((s.frame.B.erase i₀).erase i).card = m - 1 - 1 := by
    rw [Finset.card_erase_of_mem hi, hc1]
  have hpos : 0 < (s.frame.B.erase i₀).card := Finset.card_pos.2 ⟨i, hi⟩
  have hcard : (insert none ((insert j ((s.frame.B.erase i₀).erase i)).image some)).card = m := by
    rw [Finset.card_insert_of_notMem (by simp),
      Finset.card_image_of_injective _ (Option.some_injective _),
      Finset.card_insert_of_notMem hjR, hc2]
    omega
  have := (ind_iff p.point).1 (hnd _ hcard)
    (fun a => a.elim 1 (fun k => - phaseIIWeights s j θ k)) (by
      rw [sum_opt]
      simp only [Option.elim, one_smul, neg_smul, Finset.sum_neg_distrib]
      rw [← hrhs]; simp) none (by simp)
  simp at this

lemma II_pivot (hnd : p.Nondegenerate) (s : PhaseIIState p) {j i₀ : Fin n} {θ : ℝ}
    (hj : j ∉ s.frame.B) (hi₀ : i₀ ∈ s.frame.B) (hx : 0 < s.frame.x i₀ j)
    (hθ : θ = s.weight i₀ / s.frame.x i₀ j)
    (hmin : ∀ i ∈ s.frame.B, 0 < s.frame.x i j → θ ≤ s.weight i / s.frame.x i j) :
    ∃ t : PhaseIIState p, t.frame.B = insert j (s.frame.B.erase i₀) ∧
      t.weight = phaseIIWeights s j θ := by
  have hθpos : 0 < θ := by rw [hθ]; exact div_pos (s.hpositive i₀ hi₀) hx
  have hjn : j ∉ s.frame.B.erase i₀ := fun h => hj (Finset.mem_of_mem_erase h)
  have h0i₀ : s.weight i₀ - θ * s.frame.x i₀ j = 0 := by
    rw [hθ, div_mul_cancel₀ _ hx.ne', sub_self]
  have hnn : ∀ i ∈ s.frame.B, 0 ≤ s.weight i - θ * s.frame.x i j := by
    intro i hi
    rcases le_or_gt (s.frame.x i j) 0 with h | h
    · nlinarith [s.hpositive i hi]
    · have := hmin i hi h
      rw [le_div_iff₀ h] at this; linarith
  have hcard' : (insert j (s.frame.B.erase i₀)).card = m := by
    have : 0 < s.frame.B.card := Finset.card_pos.2 ⟨i₀, hi₀⟩
    rw [Finset.card_insert_of_notMem hjn, Finset.card_erase_of_mem hi₀, s.frame.hcard]
    rw [s.frame.hcard] at this
    omega
  have hind' : Ind p.col (insert j (s.frame.B.erase i₀)) :=
    pivot_ind p.col s.frame.hind s.frame.hcard hj hi₀ (c := fun i => s.frame.x i j)
      hx.ne' (II_coord p s.frame j).symm
  have hcoords : ∀ l, ∃ c : Fin n → ℝ,
      p.col l = ∑ i ∈ insert j (s.frame.B.erase i₀), c i • p.col i :=
    fun l => ind_span p.col hind' hcard' (p.col l)
  choose C hC using hcoords
  have hpos : ∀ i ∈ insert j (s.frame.B.erase i₀), 0 < phaseIIWeights s j θ i := by
    intro i hi
    rw [Finset.mem_insert] at hi
    rcases hi with h | hi
    · rw [h]; simpa [phaseIIWeights] using hθpos
    · have hiB : i ∈ s.frame.B := Finset.mem_of_mem_erase hi
      rw [II_w'_mem p s hj θ hiB]
      refine lt_of_le_of_ne (hnn i hiB) ?_
      intro h0
      exact II_tie p hnd s hj hi₀ hi h0i₀ h0.symm
  have hzero : ∀ i ∉ insert j (s.frame.B.erase i₀), phaseIIWeights s j θ i = 0 := by
    intro k hk
    have h1 : k ≠ j := fun h => hk (by simp [h])
    by_cases hkB : k ∈ s.frame.B
    · have : k = i₀ := by
        by_contra h; exact hk (by simp [h, hkB])
      rw [II_w'_mem p s hj θ hkB, this]; exact h0i₀
    · simp [phaseIIWeights, h1, hkB]
  refine ⟨⟨⟨insert j (s.frame.B.erase i₀), hcard', hind', fun i l => C l i, ?_⟩,
    phaseIIWeights s j θ, hpos, hzero, ?_, II_comb_new p s hj θ⟩, rfl, rfl⟩
  · intro l
    funext a
    have := congrFun (hC l) a
    simpa [Finset.sum_apply] using this.symm
  · intro k
    by_cases hk : k ∈ insert j (s.frame.B.erase i₀)
    · exact (hpos k hk).le
    · rw [hzero k hk]

lemma II_opt (hnd : p.Nondegenerate) (s : PhaseIIState p)
    (h : ∀ j, p.cost j ≤ s.frame.z j) : p.MaximumFeasible s.weight := by
  refine ⟨s.hfeasible, ?_⟩
  intro v hv
  have hcoef : ∀ i ∈ s.frame.B, ∑ j, v j * s.frame.x i j = s.weight i := by
    apply ind_uniq p.col s.frame.hind
    have h1 : p.rhs = ∑ j, v j • p.col j := by rw [← combine_eq, hv.2]
    have h2 : ∑ j, v j • p.col j = ∑ j, v j • ∑ i ∈ s.frame.B, s.frame.x i j • p.col i :=
      Finset.sum_congr rfl (fun j _ => by rw [II_coord])
    rw [II_weight_sum, h1, h2]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [← Finset.sum_smul]
  unfold Problem.objective
  calc ∑ j, v j * p.cost j ≤ ∑ j, v j * s.frame.z j :=
        Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h j) (hv.1 j))
    _ = ∑ i ∈ s.frame.B, s.weight i * p.cost i := by
        unfold PhaseIIFrame.z
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl; intro i hi
        rw [← hcoef i hi, Finset.sum_mul]
        apply Finset.sum_congr rfl; intro j _; ring
    _ = ∑ j, s.weight j * p.cost j := by
        apply Finset.sum_subset (Finset.subset_univ _)
        intro k _ hk; simp [s.hzero k hk]

lemma II_unbounded (s : PhaseIIState p) {j : Fin n} (hj : p.cost j > s.frame.z j)
    (hx : ∀ i ∈ s.frame.B, s.frame.x i j ≤ 0) (M : ℝ) :
    ∃ θ : ℝ, 0 < θ ∧ p.Feasible (phaseIIWeights s j θ) ∧
      M < p.objective (phaseIIWeights s j θ) ∧
      (Finset.univ.filter (fun k => 0 < phaseIIWeights s j θ k)).card = m + 1 := by
  have hj' := II_notin p s hj
  have hd : 0 < p.cost j - s.frame.z j := by linarith
  set θ : ℝ := max 1 ((M - p.objective s.weight) / (p.cost j - s.frame.z j) + 1) with hθdef
  have hθ1 : 1 ≤ θ := le_max_left _ _
  have hθpos : 0 < θ := by linarith
  have hθM : (M - p.objective s.weight) / (p.cost j - s.frame.z j) < θ :=
    lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hpos : ∀ k ∈ s.frame.B, 0 < phaseIIWeights s j θ k := by
    intro k hk
    rw [II_w'_mem p s hj' θ hk]
    nlinarith [s.hpositive k hk, hx k hk]
  have hfilter : Finset.univ.filter (fun k => 0 < phaseIIWeights s j θ k) = insert j s.frame.B := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    constructor
    · intro h
      by_contra h'
      push Not at h'
      simp [phaseIIWeights, h'.1, h'.2] at h
    · rintro (h | h)
      · rw [h]; simpa [phaseIIWeights] using hθpos
      · exact hpos k h
  refine ⟨θ, hθpos, ⟨?_, II_comb_new p s hj' θ⟩, ?_, ?_⟩
  · intro k
    by_cases hk : k ∈ insert j s.frame.B
    · rcases Finset.mem_insert.1 hk with h | h
      · rw [h]; simpa [phaseIIWeights] using hθpos.le
      · exact (hpos k h).le
    · have h1 : k ≠ j := fun h => hk (by simp [h])
      have h2 : k ∉ s.frame.B := fun h => hk (by simp [h])
      simp [phaseIIWeights, h1, h2]
  · rw [II_obj_new p s hj']
    rw [div_lt_iff₀ hd] at hθM
    linarith
  · rw [hfilter, Finset.card_insert_of_notMem hj', s.frame.hcard]


lemma II_same (s t : PhaseIIState p) (h : s.frame.B = t.frame.B) :
    p.objective s.weight = p.objective t.weight := by
  have hw : ∀ i ∈ s.frame.B, s.weight i = t.weight i :=
    ind_uniq p.col s.frame.hind (by
      rw [II_weight_sum p s]
      conv_rhs => rw [h]
      rw [II_weight_sum p t])
  rw [II_obj, II_obj, ← h]
  exact Finset.sum_congr rfl (fun i hi => by rw [hw i hi])

end PII

lemma no_run {σ : Type*} {n : ℕ} (f : ℕ → σ) (key : σ → Finset (Fin n)) (val : σ → ℝ)
    (hstep : ∀ k, val (f k) < val (f (k + 1)))
    (hkey : ∀ a b, key (f a) = key (f b) → val (f a) = val (f b)) : False := by
  have hmono : StrictMono (fun k => val (f k)) := strictMono_nat_of_lt_succ hstep
  have hinj : Function.Injective (fun k => key (f k)) := by
    intro a b hab
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have h1 : val (f a) < val (f b) := hmono h
      have := hkey a b hab; linarith
    · have h1 : val (f b) < val (f a) := hmono h
      have := hkey a b hab; linarith
  exact not_injective_infinite_finite _ hinj

theorem theorem_1_core {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate)
    (s : PhaseIIState p) (j : Fin n) (hj : p.cost j > s.frame.z j) :
    (∀ θ : ℝ, 0 < θ → p.Feasible (phaseIIWeights s j θ) →
      p.objective s.weight < p.objective (phaseIIWeights s j θ)) ∧
    (((∃ i ∈ s.frame.B, 0 < s.frame.x i j) ∧
       ∃ (i₀ : Fin n) (θ : ℝ) (t : PhaseIIState p),
         i₀ ∈ s.frame.B ∧ 0 < s.frame.x i₀ j ∧
         θ = s.weight i₀ / s.frame.x i₀ j ∧
         (∀ i ∈ s.frame.B, 0 < s.frame.x i j →
           θ ≤ s.weight i / s.frame.x i j) ∧
         t.frame.B = insert j (s.frame.B.erase i₀) ∧
         t.weight = phaseIIWeights s j θ ∧
         p.objective s.weight < p.objective t.weight) ∨
    ((∀ i ∈ s.frame.B, s.frame.x i j ≤ 0) ∧
       ∀ M : ℝ, ∃ θ : ℝ, 0 < θ ∧
         p.Feasible (phaseIIWeights s j θ) ∧
         M < p.objective (phaseIIWeights s j θ) ∧
         (Finset.univ.filter (fun k => 0 < phaseIIWeights s j θ k)).card = m + 1)) := by
  classical
  have hjB := II_notin p s hj
  have hd : 0 < p.cost j - s.frame.z j := by linarith
  refine ⟨?_, ?_⟩
  · intro θ hθ _
    rw [II_obj_new p s hjB]
    have : 0 < θ * (p.cost j - s.frame.z j) := mul_pos hθ hd
    linarith
  · by_cases h : ∃ i ∈ s.frame.B, 0 < s.frame.x i j
    · left
      refine ⟨h, ?_⟩
      have hne : (s.frame.B.filter (fun i => 0 < s.frame.x i j)).Nonempty := by
        obtain ⟨i, hi, hx⟩ := h; exact ⟨i, by simp [hi, hx]⟩
      obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image _
        (fun i => s.weight i / s.frame.x i j) hne
      simp only [Finset.mem_filter] at hi₀ hmin
      have hmin' : ∀ i ∈ s.frame.B, 0 < s.frame.x i j →
          s.weight i₀ / s.frame.x i₀ j ≤ s.weight i / s.frame.x i j :=
        fun i hi hx => hmin i ⟨hi, hx⟩
      obtain ⟨t, htB, htw⟩ := II_pivot p hnd s hjB hi₀.1 hi₀.2 rfl hmin'
      refine ⟨i₀, _, t, hi₀.1, hi₀.2, rfl, hmin', htB, htw, ?_⟩
      rw [htw, II_obj_new p s hjB]
      have hθ : 0 < s.weight i₀ / s.frame.x i₀ j := div_pos (s.hpositive i₀ hi₀.1) hi₀.2
      have : 0 < s.weight i₀ / s.frame.x i₀ j * (p.cost j - s.frame.z j) := mul_pos hθ hd
      linarith
    · right
      push Not at h
      exact ⟨h, fun M => II_unbounded p s hj h M⟩

theorem section_1_core {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate) :
    (¬ ∃ f : ℕ → PhaseIIState p, ∀ k, PhaseIIStep (f k) (f (k + 1))) ∧
    (∀ s : PhaseIIState p,
      (¬ ∃ t : PhaseIIState p, PhaseIIStep s t) →
      (∃ j : Fin n, p.cost j > s.frame.z j ∧
        (∀ i ∈ s.frame.B, s.frame.x i j ≤ 0)) ∨
      (∀ j, p.cost j ≤ s.frame.z j)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨f, hf⟩
    exact no_run f (fun s => s.frame.B) (fun s => p.objective s.weight)
      (fun k => II_step_obj p (hf k)) (fun a b h => II_same p _ _ h)
  · intro s hs
    by_cases hall : ∀ j, p.cost j ≤ s.frame.z j
    · right; exact hall
    · left
      push Not at hall
      obtain ⟨j, hj⟩ := hall
      refine ⟨j, hj, ?_⟩
      rcases (theorem_1_core p hm hmn hnd s j hj).2 with ⟨_, i₀, θ, t, hi₀, hx, hθ, hmin, hB, hw, _⟩ | ⟨hx, _⟩
      · exact absurd ⟨t, j, i₀, θ, II_notin p s hj, hi₀, hj, hx, hθ, hmin, hB, hw⟩ hs
      · exact hx


section PI
variable {m n : ℕ} (p : Problem m n) {G : Fin m → ℝ}

lemma I_card (q : PhaseIFrame p) : (insert none (q.S.image some)).card = m := by
  rw [Finset.card_insert_of_notMem (by simp),
    Finset.card_image_of_injective _ (Option.some_injective _)]
  exact q.hcard

lemma I_coord (q : PhaseIFrame p) (j : Fin n) :
    q.y0 j • p.rhs + ∑ i ∈ q.S, q.y i j • p.col i = p.col j := by
  funext a; have := congrFun (q.hcoord j) a; simpa [Finset.sum_apply] using this

def cI {p : Problem m n} (q : PhaseIFrame p) (j : Fin n) : Option (Fin n) → ℝ :=
  fun a => a.elim (q.y0 j) (fun i => q.y i j)

lemma I_coord' (q : PhaseIFrame p) (j : Fin n) :
    p.point (some j) = ∑ a ∈ insert none (q.S.image some), cI q j a • p.point a := by
  rw [sum_opt]
  simp only [cI, Option.elim]
  exact (I_coord p q j).symm

lemma I_notin (s : PhaseIState p G) {j : Fin n} (hj : 0 < s.frame.y0 j) :
    j ∉ s.frame.S := by
  intro hjS
  have := (ind_iff p.point).1 s.frame.hind
    (fun a => a.elim (s.frame.y0 j) (fun i => s.frame.y i j - if i = j then 1 else 0)) (by
      rw [sum_opt]
      simp only [Option.elim, sub_smul, Finset.sum_sub_distrib, ite_smul, one_smul, zero_smul,
        Finset.sum_ite_eq', hjS, if_true]
      have := I_coord p s.frame j
      rw [← this]; abel) none (by simp)
  simp only [Option.elim] at this
  linarith

lemma I_ref_sum (s : PhaseIState p G) :
    ∑ i ∈ s.frame.S, s.weight i • p.col i = G + s.rho • p.rhs := by
  have h := s.hreference
  rw [combine_eq] at h
  have e : (G + s.rho • p.rhs) = fun a => G a + s.rho * p.rhs a := by
    funext a; simp
  rw [e, h]
  apply Finset.sum_subset (Finset.subset_univ _)
  intro k _ hk; simp [s.hzero k hk]

lemma I_w'_mem (s : PhaseIState p G) {j : Fin n} (hj : j ∉ s.frame.S) (θ : ℝ) {k : Fin n}
    (hk : k ∈ s.frame.S) : phaseIWeights s j θ k = s.weight k - θ * s.frame.y k j := by
  have : k ≠ j := fun h => hj (h ▸ hk)
  simp [phaseIWeights, this, hk]

lemma I_comb_new (s : PhaseIState p G) {j : Fin n} (hj : j ∉ s.frame.S) (θ : ℝ) :
    p.combine (phaseIWeights s j θ) = G + (s.rho + θ * s.frame.y0 j) • p.rhs := by
  rw [combine_eq]
  have := sum_piece (S := s.frame.S) hj (fun k r => r • p.col k) (by simp) θ
    (fun k => s.weight k - θ * s.frame.y k j)
  beta_reduce at this
  simp only [phaseIWeights]
  rw [this]
  have hY : ∑ i ∈ s.frame.S, s.frame.y i j • p.col i = p.col j - s.frame.y0 j • p.rhs := by
    rw [← I_coord p s.frame j]; abel
  simp only [sub_smul, Finset.sum_sub_distrib, mul_smul, ← Finset.smul_sum, I_ref_sum, hY]
  module

lemma I_step_rho {s t : PhaseIState p G} (h : PhaseIStep s t) : s.rho < t.rho := by
  obtain ⟨j, i₀, θ, hjS, hi₀, hy0, hy, hθ, hmin, hS, hw, hr⟩ := h
  have hθpos : 0 < θ := by rw [hθ]; exact div_pos (s.hpositive i₀ hi₀) hy
  rw [hr]
  have : 0 < θ * s.frame.y0 j := mul_pos hθpos hy0
  linarith

lemma I_same (s t : PhaseIState p G) (h : s.frame.S = t.frame.S) : s.rho = t.rho := by
  have e1 := I_ref_sum p s
  have e2 := I_ref_sum p t
  rw [← h] at e2
  have := (ind_iff p.point).1 s.frame.hind
    (fun a => a.elim (s.rho - t.rho) (fun i => -(s.weight i - t.weight i))) (by
      rw [sum_opt]
      simp only [Option.elim, neg_smul, sub_smul, Finset.sum_neg_distrib, Finset.sum_sub_distrib]
      rw [e1, e2]; module) none (by simp)
  simp only [Option.elim] at this
  linarith

lemma I_tie (hgp : GeneralPosition p G) (s : PhaseIState p G) {j i₀ i : Fin n} {θ : ℝ}
    (hj : j ∉ s.frame.S) (hi₀ : i₀ ∈ s.frame.S) (hi : i ∈ s.frame.S.erase i₀)
    (h0i₀ : s.weight i₀ - θ * s.frame.y i₀ j = 0)
    (h0 : s.weight i - θ * s.frame.y i j = 0) : False := by
  have hiS : i ∈ s.frame.S := Finset.mem_of_mem_erase hi
  have hjR : j ∉ (s.frame.S.erase i₀).erase i := fun h =>
    hj (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hsupp : ∀ k, k ∉ insert j ((s.frame.S.erase i₀).erase i) →
      phaseIWeights s j θ k = 0 := by
    intro k hk
    by_cases hkS : k ∈ s.frame.S
    · rw [I_w'_mem p s hj θ hkS]
      by_cases h1 : k = i₀
      · rw [h1]; exact h0i₀
      · by_cases h2 : k = i
        · rw [h2]; exact h0
        · exfalso; apply hk
          by_cases h3 : k = j
          · simp [h3]
          · simp [h1, h2, hkS]
    · have : k ≠ j := fun h => hk (by simp [h])
      simp [phaseIWeights, this, hkS]
  have hrhs : G + (s.rho + θ * s.frame.y0 j) • p.rhs = ∑ k ∈ insert j ((s.frame.S.erase i₀).erase i),
      phaseIWeights s j θ k • p.col k := by
    rw [← I_comb_new p s hj θ, combine_eq]
    exact (Finset.sum_subset (Finset.subset_univ _) (fun k _ hk => by simp [hsupp k hk])).symm
  have hS := s.frame.hcard
  have hc1 : (s.frame.S.erase i₀).card = s.frame.S.card - 1 := Finset.card_erase_of_mem hi₀
  have hc2 : ((s.frame.S.erase i₀).erase i).card = s.frame.S.card - 1 - 1 := by
    rw [Finset.card_erase_of_mem hi, hc1]
  have hpos : 0 < (s.frame.S.erase i₀).card := Finset.card_pos.2 ⟨i, hi⟩
  have hn1 : (none : Option (Option (Fin n))) ∉
      insert (some none) ((insert j ((s.frame.S.erase i₀).erase i)).image (fun k => some (some k))) := by
    simp
  have hn2 : (some none : Option (Option (Fin n))) ∉
      (insert j ((s.frame.S.erase i₀).erase i)).image (fun k => some (some k)) := by
    simp
  have hinj : Function.Injective (fun k : Fin n => (some (some k) : Option (Option (Fin n)))) :=
    fun a b h => by simpa using h
  have hcard : (insert none (insert (some none)
      ((insert j ((s.frame.S.erase i₀).erase i)).image (fun k => some (some k))))).card = m := by
    rw [Finset.card_insert_of_notMem hn1, Finset.card_insert_of_notMem hn2,
      Finset.card_image_of_injective _ hinj, Finset.card_insert_of_notMem hjR, hc2]
    omega
  have hind := hgp _ hcard (by simp) (by simp)
  have := (ind_iff (augmentedPoint p G)).1 hind
    (fun a => a.elim 1 (fun b => b.elim (s.rho + θ * s.frame.y0 j)
      (fun k => - phaseIWeights s j θ k))) (by
      rw [Finset.sum_insert hn1, Finset.sum_insert hn2, Finset.sum_image (fun a _ b _ h => hinj h)]
      simp only [augmentedPoint, Option.elim, one_smul, neg_smul, Finset.sum_neg_distrib]
      rw [← hrhs]; abel) none (by simp)
  simp at this

lemma I_pivot (hgp : GeneralPosition p G) (s : PhaseIState p G) {j i₀ : Fin n} {θ : ℝ}
    (hj : j ∉ s.frame.S) (hi₀ : i₀ ∈ s.frame.S) (hy0 : 0 < s.frame.y0 j)
    (hy : 0 < s.frame.y i₀ j)
    (hθ : θ = s.weight i₀ / s.frame.y i₀ j)
    (hmin : ∀ i ∈ s.frame.S, 0 < s.frame.y i j → θ ≤ s.weight i / s.frame.y i j) :
    ∃ t : PhaseIState p G, t.frame.S = insert j (s.frame.S.erase i₀) ∧
      t.weight = phaseIWeights s j θ ∧ t.rho = s.rho + θ * s.frame.y0 j := by
  have hθpos : 0 < θ := by rw [hθ]; exact div_pos (s.hpositive i₀ hi₀) hy
  have hjn : j ∉ s.frame.S.erase i₀ := fun h => hj (Finset.mem_of_mem_erase h)
  have h0i₀ : s.weight i₀ - θ * s.frame.y i₀ j = 0 := by
    rw [hθ, div_mul_cancel₀ _ hy.ne', sub_self]
  have hnn : ∀ i ∈ s.frame.S, 0 ≤ s.weight i - θ * s.frame.y i j := by
    intro i hi
    rcases le_or_gt (s.frame.y i j) 0 with h | h
    · nlinarith [s.hpositive i hi]
    · have := hmin i hi h
      rw [le_div_iff₀ h] at this; linarith
  have hpos0 : 0 < s.frame.S.card := Finset.card_pos.2 ⟨i₀, hi₀⟩
  have hcardS : (insert j (s.frame.S.erase i₀)).card + 1 = m := by
    rw [Finset.card_insert_of_notMem hjn, Finset.card_erase_of_mem hi₀]
    have := s.frame.hcard
    omega
  have hcard' : (insert none ((insert j (s.frame.S.erase i₀)).image some)).card = m := by
    rw [Finset.card_insert_of_notMem (by simp),
      Finset.card_image_of_injective _ (Option.some_injective _)]
    exact hcardS
  have hjT : (some j : Option (Fin n)) ∉ insert none (s.frame.S.image some) := by
    simp [hj]
  have hiT : (some i₀ : Option (Fin n)) ∈ insert none (s.frame.S.image some) := by
    simp [hi₀]
  have e : insert (some j) ((insert none (s.frame.S.image some)).erase (some i₀))
      = insert none ((insert j (s.frame.S.erase i₀)).image some) := by
    ext a
    rcases a with _ | a
    · simp
    · simp [Finset.mem_erase]
  have hind' : Ind p.point (insert none ((insert j (s.frame.S.erase i₀)).image some)) := by
    rw [← e]
    exact pivot_ind p.point s.frame.hind (I_card p s.frame) hjT hiT (c := cI s.frame j)
      (by simp [cI]; exact hy.ne') (I_coord' p s.frame j)
  have hcoords : ∀ l, ∃ c : Option (Fin n) → ℝ,
      p.col l = ∑ a ∈ insert none ((insert j (s.frame.S.erase i₀)).image some),
        c a • p.point a :=
    fun l => ind_span p.point hind' hcard' (p.col l)
  choose C hC using hcoords
  have hpos : ∀ i ∈ insert j (s.frame.S.erase i₀), 0 < phaseIWeights s j θ i := by
    intro i hi
    rw [Finset.mem_insert] at hi
    rcases hi with h | hi
    · rw [h]; simpa [phaseIWeights] using hθpos
    · have hiS : i ∈ s.frame.S := Finset.mem_of_mem_erase hi
      rw [I_w'_mem p s hj θ hiS]
      refine lt_of_le_of_ne (hnn i hiS) ?_
      intro h0
      exact I_tie p hgp s hj hi₀ hi h0i₀ h0.symm
  have hzero : ∀ i ∉ insert j (s.frame.S.erase i₀), phaseIWeights s j θ i = 0 := by
    intro k hk
    have h1 : k ≠ j := fun h => hk (by simp [h])
    by_cases hkS : k ∈ s.frame.S
    · have : k = i₀ := by
        by_contra h; exact hk (by simp [h, hkS])
      rw [I_w'_mem p s hj θ hkS, this]; exact h0i₀
    · simp [phaseIWeights, h1, hkS]
  have hrho : 0 < s.rho + θ * s.frame.y0 j := by
    have := s.hrho
    have : 0 < θ * s.frame.y0 j := mul_pos hθpos hy0
    linarith
  refine ⟨⟨⟨insert j (s.frame.S.erase i₀), hcardS, hind', fun l => C l none,
    fun i l => C l (some i), ?_⟩, phaseIWeights s j θ, s.rho + θ * s.frame.y0 j, hrho,
    hpos, hzero, ?_⟩, rfl, rfl, rfl⟩
  · intro l
    funext a
    have := congrFun (hC l) a
    rw [sum_opt] at this
    simpa [Finset.sum_apply] using this.symm
  · have := I_comb_new p s hj θ
    funext a
    have h2 := congrFun this a
    rw [h2]; simp

lemma I_step_exists (hgp : GeneralPosition p G) (s : PhaseIState p G) {j : Fin n}
    (hj0 : 0 < s.frame.y0 j) (hjS : j ∉ s.frame.S)
    (h : ∃ i ∈ s.frame.S, 0 < s.frame.y i j) : ∃ t, PhaseIStep s t := by
  classical
  have hne : (s.frame.S.filter (fun i => 0 < s.frame.y i j)).Nonempty := by
    obtain ⟨i, hi, hx⟩ := h; exact ⟨i, by simp [hi, hx]⟩
  obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image _
    (fun i => s.weight i / s.frame.y i j) hne
  simp only [Finset.mem_filter] at hi₀ hmin
  have hmin' : ∀ i ∈ s.frame.S, 0 < s.frame.y i j →
      s.weight i₀ / s.frame.y i₀ j ≤ s.weight i / s.frame.y i j :=
    fun i hi hx => hmin i ⟨hi, hx⟩
  obtain ⟨t, htS, htw, htr⟩ := I_pivot p hgp s hjS hi₀.1 hj0 hi₀.2 rfl hmin'
  exact ⟨t, j, i₀, _, hjS, hi₀.1, hj0, hi₀.2, rfl, hmin', htS, htw, htr⟩


lemma I_strict (hnd : p.Nondegenerate) (s : PhaseIState p G) {j : Fin n}
    (hjS : j ∉ s.frame.S) (hy : ∀ i ∈ s.frame.S, s.frame.y i j ≤ 0) :
    ∀ i ∈ s.frame.S, s.frame.y i j < 0 := by
  intro i hi
  refine lt_of_le_of_ne (hy i hi) ?_
  intro h0
  have hn1 : (some j : Option (Fin n)) ∉ (s.frame.S.erase i).image some := by
    simp [hjS]
  have hn2 : (none : Option (Fin n)) ∉ insert (some j) ((s.frame.S.erase i).image some) := by
    simp
  have hcard : (insert none (insert (some j) ((s.frame.S.erase i).image some))).card = m := by
    rw [Finset.card_insert_of_notMem hn2, Finset.card_insert_of_notMem hn1,
      Finset.card_image_of_injective _ (Option.some_injective _), Finset.card_erase_of_mem hi]
    have := s.frame.hcard
    have := Finset.card_pos.2 (⟨i, hi⟩ : s.frame.S.Nonempty)
    omega
  have := (ind_iff p.point).1 (hnd _ hcard)
    (fun a => a.elim (s.frame.y0 j) (fun k => if k = j then -1 else s.frame.y k j)) (by
      rw [Finset.sum_insert hn2, Finset.sum_insert hn1,
        Finset.sum_image (fun a _ b _ h => Option.some_injective _ h)]
      have hcong : ∑ k ∈ s.frame.S.erase i, (if k = j then (-1 : ℝ) else s.frame.y k j) • p.col k
          = ∑ k ∈ s.frame.S.erase i, s.frame.y k j • p.col k := by
        apply Finset.sum_congr rfl
        intro k hk
        have : k ≠ j := fun h => hjS (h ▸ Finset.mem_of_mem_erase hk)
        simp [this]
      have hE : ∑ k ∈ s.frame.S.erase i, s.frame.y k j • p.col k
          = ∑ k ∈ s.frame.S, s.frame.y k j • p.col k :=
        Finset.sum_erase _ (by rw [h0]; simp)
      simp only [Option.elim, if_true]
      show s.frame.y0 j • p.rhs + ((-1 : ℝ) • p.col j +
        ∑ k ∈ s.frame.S.erase i, (if k = j then (-1 : ℝ) else s.frame.y k j) • p.col k) = 0
      rw [hcong, hE, ← I_coord p s.frame j]
      module) (some j) (by simp)
  simp at this

lemma I_handoff (hnd : p.Nondegenerate) (s : PhaseIState p G) {j : Fin n}
    (hj0 : 0 < s.frame.y0 j) (hy : ∀ i ∈ s.frame.S, s.frame.y i j ≤ 0) :
    ∃ t : PhaseIIState p, HandOff s t := by
  have hjS := I_notin p s hj0
  have hstrict := I_strict p hnd s hjS hy
  have hcard : (insert j s.frame.S).card = m := by
    rw [Finset.card_insert_of_notMem hjS]; exact s.frame.hcard
  have hY : ∑ i ∈ s.frame.S, s.frame.y i j • p.col i = p.col j - s.frame.y0 j • p.rhs := by
    rw [← I_coord p s.frame j]; abel
  have hind : Ind p.col (insert j s.frame.S) := by
    rw [ind_iff]
    intro g hg
    rw [Finset.sum_insert hjS] at hg
    have := (ind_iff p.point).1 s.frame.hind
      (fun a => a.elim (g j * s.frame.y0 j) (fun i => g i + g j * s.frame.y i j)) (by
        rw [sum_opt]
        simp only [Option.elim, add_smul, Finset.sum_add_distrib, mul_smul, ← Finset.smul_sum, hY]
        rw [← hg]; module)
    have h0 := this none (by simp)
    simp only [Option.elim] at h0
    have hgj : g j = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact h
      · exact absurd h hj0.ne'
    intro i hi
    rcases Finset.mem_insert.1 hi with h | h
    · rw [h]; exact hgj
    · have := this (some i) (by simp [h])
      simp only [Option.elim, hgj] at this
      linarith
  have hcoords : ∀ l, ∃ c : Fin n → ℝ,
      p.col l = ∑ i ∈ insert j s.frame.S, c i • p.col i :=
    fun l => ind_span p.col hind hcard (p.col l)
  choose C hC using hcoords
  have hpos : ∀ i ∈ insert j s.frame.S, 0 < handoffWeights s j i := by
    intro i hi
    rcases Finset.mem_insert.1 hi with h | h
    · rw [h]; simpa [handoffWeights] using hj0
    · have : i ≠ j := fun h' => hjS (h' ▸ h)
      simp only [handoffWeights, this, h, if_true, if_false]
      exact div_pos (by linarith [hstrict i h]) hj0
  have hzero : ∀ i ∉ insert j s.frame.S, handoffWeights s j i = 0 := by
    intro k hk
    have h1 : k ≠ j := fun h => hk (by simp [h])
    have h2 : k ∉ s.frame.S := fun h => hk (by simp [h])
    simp [handoffWeights, h1, h2]
  have hcomb : p.combine (handoffWeights s j) = p.rhs := by
    rw [combine_eq]
    have := sum_piece (S := s.frame.S) hjS (fun k r => r • p.col k) (by simp) (1 / s.frame.y0 j)
      (fun k => -(s.frame.y k j) / s.frame.y0 j)
    beta_reduce at this
    simp only [handoffWeights]
    rw [this]
    have e : ∀ k ∈ s.frame.S, (-(s.frame.y k j) / s.frame.y0 j) • p.col k
        = (-(1 / s.frame.y0 j)) • (s.frame.y k j • p.col k) := by
      intro k _
      rw [smul_smul]; congr 1; ring
    rw [Finset.sum_congr rfl e, ← Finset.smul_sum, hY]
    have hne : s.frame.y0 j ≠ 0 := hj0.ne'
    match_scalars <;> field_simp <;> ring
  refine ⟨⟨⟨insert j s.frame.S, hcard, hind, fun i l => C l i, ?_⟩, handoffWeights s j, hpos, hzero,
    ?_, hcomb⟩, j, hjS, hj0, hy, rfl, rfl⟩
  · intro l
    funext a
    have := congrFun (hC l) a
    simpa [Finset.sum_apply] using this.symm
  · intro k
    by_cases hk : k ∈ insert j s.frame.S
    · exact (hpos k hk).le
    · rw [hzero k hk]

lemma I_infeasible (s : PhaseIState p G) (h : ∀ j, s.frame.y0 j ≤ 0) (w : Fin n → ℝ)
    (hw : p.Feasible w) : False := by
  have h1 : p.rhs = ∑ j, w j • p.col j := by rw [← combine_eq, hw.2]
  have h2 : ∑ j, w j • p.col j = (∑ j, w j * s.frame.y0 j) • p.rhs
      + ∑ i ∈ s.frame.S, (∑ j, w j * s.frame.y i j) • p.col i := by
    have : ∀ j, w j • p.col j = (w j * s.frame.y0 j) • p.rhs
        + ∑ i ∈ s.frame.S, (w j * s.frame.y i j) • p.col i := by
      intro j
      conv_lhs => rw [← I_coord p s.frame j]
      simp only [smul_add, Finset.smul_sum, smul_smul]
    simp_rw [this, Finset.sum_add_distrib, ← Finset.sum_smul]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.sum_smul]
  have hσ : ∑ j, w j * s.frame.y0 j ≤ 0 :=
    Finset.sum_nonpos (fun j _ => mul_nonpos_of_nonneg_of_nonpos (hw.1 j) (h j))
  have := (ind_iff p.point).1 s.frame.hind
    (fun a => a.elim ((∑ j, w j * s.frame.y0 j) - 1) (fun i => ∑ j, w j * s.frame.y i j)) (by
      rw [sum_opt]
      simp only [Option.elim, sub_smul, one_smul]
      rw [← h1] at h2
      -- h2 : rhs = σ • rhs + Σ ...
      have := h2
      rw [add_comm] at this
      calc _ = (∑ j, w j * s.frame.y0 j) • p.rhs + ∑ i ∈ s.frame.S,
            (∑ j, w j * s.frame.y i j) • p.col i - p.rhs := by abel
        _ = 0 := by rw [← h2]; abel) none (by simp)
  simp only [Option.elim] at this
  linarith

end PI

theorem section_2_core {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate)
    (G : Fin m → ℝ) (hgp : GeneralPosition p G)
    (initial : PhaseIState p G) :
    (¬ ∃ f : ℕ → PhaseIState p G, ∀ k, PhaseIStep (f k) (f (k + 1))) ∧
    (∀ s : PhaseIState p G,
      (¬ ∃ t : PhaseIState p G, PhaseIStep s t) →
      ((∀ j, s.frame.y0 j ≤ 0) ∧ (∀ w, ¬ p.Feasible w)) ∨
      (∃ j : Fin n, 0 < s.frame.y0 j ∧
        (∀ i ∈ s.frame.S, s.frame.y i j ≤ 0) ∧
        ∃ t : PhaseIIState p, HandOff s t)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨f, hf⟩
    exact no_run f (fun s => s.frame.S) (fun s => s.rho)
      (fun k => I_step_rho p (hf k)) (fun a b h => I_same p _ _ h)
  · intro s hs
    by_cases hpos : ∃ j, 0 < s.frame.y0 j
    · right
      obtain ⟨j, hj⟩ := hpos
      have hjS := I_notin p s hj
      have hy : ∀ i ∈ s.frame.S, s.frame.y i j ≤ 0 := by
        intro i hi
        by_contra h
        push Not at h
        obtain ⟨t, ht⟩ := I_step_exists p hgp s hj hjS ⟨i, hi, h⟩
        exact hs ⟨t, ht⟩
      obtain ⟨t, ht⟩ := I_handoff p hnd s hj hy
      exact ⟨j, hj, hy, t, ht⟩
    · left
      push Not at hpos
      exact ⟨hpos, fun w hw => I_infeasible p s hpos w hw⟩


theorem simplex_core {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate)
    (G : Fin m → ℝ) (hgp : GeneralPosition p G)
    (initial : PhaseIState p G) :
    (¬ ∃ f : ℕ → SimplexState p G,
      ∀ k, SimplexStep (f k) (f (k + 1))) ∧
    (∀ s : SimplexState p G, Terminal s →
      (∃ u : PhaseIState p G, s = Sum.inl u ∧
        (∀ j, u.frame.y0 j ≤ 0) ∧ (∀ w, ¬ p.Feasible w)) ∨
      (∃ u : PhaseIIState p, s = Sum.inr u ∧
        ∃ j : Fin n, p.cost j > u.frame.z j ∧
          (∀ i ∈ u.frame.B, u.frame.x i j ≤ 0) ∧ p.Unbounded) ∨
      (∃ u : PhaseIIState p, s = Sum.inr u ∧
        (∀ j, p.cost j ≤ u.frame.z j) ∧ p.MaximumFeasible u.weight)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨f, hf⟩
    by_cases hex : ∃ k, ∃ u, f k = Sum.inr u
    · obtain ⟨k, u, hu⟩ := hex
      have hall : ∀ N, ∃ u : PhaseIIState p, f (k + N) = Sum.inr u := by
        intro N
        induction N with
        | zero => exact ⟨u, hu⟩
        | succ N ih =>
          obtain ⟨v, hv⟩ := ih
          have h := hf (k + N)
          rw [hv] at h
          generalize hz : f (k + N + 1) = z at h
          cases h with
          | phaseII hs => exact ⟨_, rfl⟩
      choose g hg using hall
      refine (section_1_core p hm hmn hnd).1 ⟨g, fun N => ?_⟩
      have h := hf (k + N)
      rw [hg N, show k + N + 1 = k + (N + 1) from rfl, hg (N + 1)] at h
      cases h with
      | phaseII hs => exact hs
    · push Not at hex
      have hall : ∀ k, ∃ u : PhaseIState p G, f k = Sum.inl u := by
        intro k
        cases hk : f k with
        | inl u => exact ⟨u, rfl⟩
        | inr u => exact absurd hk (hex k u)
      choose g hg using hall
      refine (section_2_core p hm hmn hnd G hgp initial).1 ⟨g, fun N => ?_⟩
      have h := hf N
      rw [hg N, hg (N + 1)] at h
      cases h with
      | phaseI hs => exact hs
  · intro s hs
    unfold Terminal at hs
    rcases s with u | u
    · have hnoI : ¬ ∃ t, PhaseIStep u t := fun ⟨t, ht⟩ => hs ⟨Sum.inl t, SimplexStep.phaseI ht⟩
      rcases (section_2_core p hm hmn hnd G hgp initial).2 u hnoI with ⟨h1, h2⟩ | ⟨j, _, _, t, ht⟩
      · left; exact ⟨u, rfl, h1, h2⟩
      · exact absurd ⟨Sum.inr t, SimplexStep.handoff ht⟩ hs
    · have hnoII : ¬ ∃ t, PhaseIIStep u t := fun ⟨t, ht⟩ => hs ⟨Sum.inr t, SimplexStep.phaseII ht⟩
      rcases (section_1_core p hm hmn hnd).2 u hnoII with ⟨j, hj, hx⟩ | hall
      · right; left
        refine ⟨u, rfl, j, hj, hx, fun M => ?_⟩
        obtain ⟨θ, _, hf, hM, _⟩ := II_unbounded p u hj hx M
        exact ⟨_, hf, hM⟩
      · right; right
        exact ⟨u, rfl, hall, II_opt p hnd u hall⟩

end DantzigSimplex.Technique

open DantzigSimplex.Technique


theorem solution {m n : ℕ} (p : Problem m n)
    (hm : 1 ≤ m) (hmn : m ≤ n) (hnd : p.Nondegenerate)
    (G : Fin m → ℝ) (hgp : GeneralPosition p G)
    (initial : PhaseIState p G) :
    (¬ ∃ f : ℕ → SimplexState p G,
      ∀ k, SimplexStep (f k) (f (k + 1))) ∧
    (∀ s : SimplexState p G, Terminal s →
      (∃ u : PhaseIState p G, s = Sum.inl u ∧
        (∀ j, u.frame.y0 j ≤ 0) ∧ (∀ w, ¬ p.Feasible w)) ∨
      (∃ u : PhaseIIState p, s = Sum.inr u ∧
        ∃ j : Fin n, p.cost j > u.frame.z j ∧
          (∀ i ∈ u.frame.B, u.frame.x i j ≤ 0) ∧ p.Unbounded) ∨
      (∃ u : PhaseIIState p, s = Sum.inr u ∧
        (∀ j, p.cost j ≤ u.frame.z j) ∧ p.MaximumFeasible u.weight)) := by
  exact simplex_core p hm hmn hnd G hgp initial
