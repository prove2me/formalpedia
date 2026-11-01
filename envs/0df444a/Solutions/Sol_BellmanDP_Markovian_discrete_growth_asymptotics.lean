-- Prove2me | solution 1 for BellmanDP.Markovian.discrete_growth_asymptotics
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-31T08:26:55.93305+00:00
-- url     : https://prove2.me/submissions/d39ea50f-33d2-4d3a-b9d9-24583696ab63

import Mathlib
import Definitions.Def_BellmanDP_Markovian_Discrete

section
open Finset
namespace BellmanDP.Markovian.Fresh
variable {N : ℕ} {Q : Fin N → Type*}
variable {a : (i : Fin N) → Q i → Fin N → ℝ} {S : (i : Fin N) → Set (Q i)} {m : ℝ}

lemma maxIter_step_greatest (h : MarkovHyp a S m) (c : Fin N → ℝ) (n : ℕ) (i : Fin N) :
    IsGreatest ((fun q => ∑ j, a i q j * maxIter a S c n j) '' S i)
      (maxIter a S c (n+1) i) := by
  obtain ⟨q,hq,hmax⟩ := h.attain (maxIter a S c n) i
  have hg : IsGreatest ((fun q => ∑ j, a i q j * maxIter a S c n j) '' S i)
      (∑ j, a i q j * maxIter a S c n j) := by
    refine ⟨⟨q,hq,rfl⟩, ?_⟩
    rintro _ ⟨q',hq',rfl⟩
    exact hmax q' hq'
  simpa only [maxIter, hg.csSup_eq] using hg

lemma row_le_maxIter_step (h : MarkovHyp a S m) (c : Fin N → ℝ) (n : ℕ)
    (i : Fin N) (q : Q i) (hq : q ∈ S i) :
    (∑ j, a i q j * maxIter a S c n j) ≤ maxIter a S c (n+1) i :=
  (maxIter_step_greatest h c n i).2 ⟨q,hq,rfl⟩

lemma maxIter_nonneg (h : MarkovHyp a S m) {c : Fin N → ℝ} (hc : ∀ i, 0 ≤ c i) :
    ∀ n i, 0 ≤ maxIter a S c n i := by
  intro n
  induction n with
  | zero => exact hc
  | succ n ih =>
    intro i
    obtain ⟨q,hq,he⟩ := (maxIter_step_greatest h c n i).1
    rw [← he]
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (h.pos i q hq j).le (ih j))

lemma maxIter_one_pos (h : MarkovHyp a S m) {c : Fin N → ℝ}
    (hc : ∀ i, 0 ≤ c i) (hc0 : c ≠ 0) (i : Fin N) :
    0 < maxIter a S c 1 i := by
  have hex : ∃ j, 0 < c j := by
    by_contra hn
    push Not at hn
    apply hc0
    funext j
    exact le_antisymm (hn j) (hc j)
  obtain ⟨j,hj⟩ := hex
  obtain ⟨q,hq,he⟩ := (maxIter_step_greatest h c 0 i).1
  rw [← he]
  apply Finset.sum_pos'
  · intro b hb
    exact mul_nonneg (h.pos i q hq b).le (hc b)
  · exact ⟨j, Finset.mem_univ _, mul_pos (h.pos i q hq j) hj⟩

end BellmanDP.Markovian.Fresh
end

section
open Finset
namespace BellmanDP.Markovian.Fresh
variable {N : ℕ} {Q : Fin N → Type*}
variable {a : (i : Fin N) → Q i → Fin N → ℝ} {S : (i : Fin N) → Set (Q i)}
variable {lam : ℝ} {y : Fin N → ℝ}

noncomputable def rowWeight (a : (i : Fin N) → Q i → Fin N → ℝ) (lam : ℝ) (y : Fin N → ℝ)
    (i : Fin N) (q : Q i) (j : Fin N) : ℝ := a i q j * y j / (lam * y i)

lemma rowWeight_pos {m : ℝ} (h : MarkovHyp a S m) (hlam : 0 < lam)
    (hy : ∀ i, 0 < y i) (i : Fin N) (q : Q i) (hq : q ∈ S i) (j : Fin N) :
    0 < rowWeight a lam y i q j := by
  exact div_pos (mul_pos (h.pos i q hq j) (hy j)) (mul_pos hlam (hy i))

lemma rowWeight_sum_le (hey : IsMaxEigenpair a S lam y) (hlam : 0 < lam)
    (hy : ∀ i, 0 < y i) (i : Fin N) (q : Q i) (hq : q ∈ S i) :
    (∑ j, rowWeight a lam y i q j) ≤ 1 := by
  unfold rowWeight
  rw [← Finset.sum_div]
  apply (div_le_one (mul_pos hlam (hy i))).mpr
  exact (hey i).2 ⟨q,hq,rfl⟩

lemma exists_stochastic_policy (hey : IsMaxEigenpair a S lam y)
    (hlam : 0 < lam) (hy : ∀ i, 0 < y i) :
    ∃ qs : (i : Fin N) → Q i, (∀ i, qs i ∈ S i) ∧
      ∀ i, (∑ j, rowWeight a lam y i (qs i) j) = 1 := by
  classical
  have hex : ∀ i, ∃ q ∈ S i, (∑ j, a i q j * y j) = lam * y i :=
    fun i => (hey i).1
  choose qs hq he using hex
  refine ⟨qs,hq,?_⟩
  intro i
  unfold rowWeight
  rw [← Finset.sum_div, he i, div_self (ne_of_gt (mul_pos hlam (hy i)))]

lemma substochastic_upper {ι : Type*} [Fintype ι] (p z : ι → ℝ) (U : ℝ)
    (hp : ∀ j, 0 ≤ p j) (hs : (∑ j,p j) ≤ 1) (hU : 0 ≤ U)
    (hz : ∀ j, z j ≤ U) : (∑ j, p j*z j) ≤ U := by
  calc
    _ ≤ ∑ j, p j*U := Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hz j) (hp j))
    _ = (∑ j,p j)*U := (Finset.sum_mul _ _ _).symm
    _ ≤ 1*U := mul_le_mul_of_nonneg_right hs hU
    _ = U := one_mul U

end BellmanDP.Markovian.Fresh
end

section
open Finset
namespace BellmanDP.Markovian.Fresh
variable {N : ℕ} {Q : Fin N → Type*}
variable {a : (i : Fin N) → Q i → Fin N → ℝ} {S : (i : Fin N) → Set (Q i)}
variable {m lam : ℝ} {y c : Fin N → ℝ}

noncomputable def normalizedIter (a : (i : Fin N) → Q i → Fin N → ℝ)
    (S : (i : Fin N) → Set (Q i)) (c : Fin N → ℝ) (lam : ℝ) (y : Fin N → ℝ)
    (n : ℕ) (i : Fin N) : ℝ := maxIter a S c n i / (lam ^ n * y i)

lemma normalized_row_identity (hlam : 0 < lam) (hy : ∀ i, 0 < y i)
    (n : ℕ) (i : Fin N) (q : Q i) :
    (∑ j, rowWeight a lam y i q j * normalizedIter a S c lam y n j) =
    (∑ j, a i q j * maxIter a S c n j) / (lam ^ (n+1) * y i) := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  unfold rowWeight normalizedIter
  have hl := ne_of_gt hlam
  have hi := ne_of_gt (hy i)
  have hj := ne_of_gt (hy j)
  rw [pow_succ]
  field_simp

lemma normalizedIter_nonneg (h : MarkovHyp a S m) (hc : ∀ i, 0 ≤ c i)
    (hlam : 0 < lam) (hy : ∀ i, 0 < y i) (n : ℕ) (i : Fin N) :
    0 ≤ normalizedIter a S c lam y n i :=
  div_nonneg (maxIter_nonneg h hc n i) (mul_pos (pow_pos hlam n) (hy i)).le

lemma normalizedIter_one_pos (h : MarkovHyp a S m) (hc : ∀ i, 0 ≤ c i)
    (hc0 : c ≠ 0) (hlam : 0 < lam) (hy : ∀ i, 0 < y i) (i : Fin N) :
    0 < normalizedIter a S c lam y 1 i :=
  div_pos (maxIter_one_pos h hc hc0 i) (mul_pos (pow_pos hlam 1) (hy i))

lemma normalized_row_le (h : MarkovHyp a S m) (hlam : 0 < lam)
    (hy : ∀ i, 0 < y i) (n : ℕ) (i : Fin N) (q : Q i) (hq : q ∈ S i) :
    (∑ j, rowWeight a lam y i q j * normalizedIter a S c lam y n j) ≤
      normalizedIter a S c lam y (n+1) i := by
  rw [normalized_row_identity hlam hy]
  exact div_le_div_of_nonneg_right (row_le_maxIter_step h c n i q hq)
    (mul_pos (pow_pos hlam (n+1)) (hy i)).le

lemma normalized_step_attained (h : MarkovHyp a S m) (hlam : 0 < lam)
    (hy : ∀ i, 0 < y i) (n : ℕ) (i : Fin N) :
    ∃ q ∈ S i, normalizedIter a S c lam y (n+1) i =
      ∑ j, rowWeight a lam y i q j * normalizedIter a S c lam y n j := by
  obtain ⟨q,hq,he⟩ := (maxIter_step_greatest h c n i).1
  refine ⟨q,hq,?_⟩
  rw [normalized_row_identity hlam hy]
  exact congrArg (fun z : ℝ => z / (lam ^ (n+1) * y i)) he.symm

end BellmanDP.Markovian.Fresh
end

section
open Finset
namespace BellmanDP.Markovian.Fresh
noncomputable section
variable {ι : Type*} [Fintype ι] [Nonempty ι]

def minCoord (z : ι → ℝ) : ℝ := Finset.univ.inf' Finset.univ_nonempty z
def maxCoord (z : ι → ℝ) : ℝ := Finset.univ.sup' Finset.univ_nonempty z

lemma minCoord_le (z : ι → ℝ) (i : ι) : minCoord z ≤ z i :=
  Finset.inf'_le z (Finset.mem_univ i)
lemma le_maxCoord (z : ι → ℝ) (i : ι) : z i ≤ maxCoord z :=
  Finset.le_sup' z (Finset.mem_univ i)
lemma le_minCoord {z : ι → ℝ} {a : ℝ} (h : ∀ i, a ≤ z i) : a ≤ minCoord z :=
  Finset.le_inf' _ _ (fun i _ => h i)
lemma maxCoord_le {z : ι → ℝ} {a : ℝ} (h : ∀ i, z i ≤ a) : maxCoord z ≤ a :=
  Finset.sup'_le _ _ (fun i _ => h i)
lemma exists_minCoord (z : ι → ℝ) : ∃ i, z i = minCoord z := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_inf' Finset.univ_nonempty z
  exact ⟨i,hi.symm⟩
lemma exists_maxCoord (z : ι → ℝ) : ∃ i, z i = maxCoord z := by
  obtain ⟨i,_,hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty z
  exact ⟨i,hi.symm⟩
lemma minCoord_le_maxCoord (z : ι → ℝ) : minCoord z ≤ maxCoord z := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact (minCoord_le z i).trans (le_maxCoord z i)
lemma minCoord_pos {z : ι → ℝ} (h : ∀ i, 0 < z i) : 0 < minCoord z := by
  obtain ⟨i,hi⟩ := exists_minCoord z
  rw [← hi]
  exact h i

end
end BellmanDP.Markovian.Fresh
end

section
open Finset
namespace BellmanDP.Markovian.Fresh
variable {ι : Type*} [Fintype ι] [Nonempty ι]

lemma exists_positive_minorant (P : ι → ι → ℝ) (hP : ∀ i j, 0 < P i j) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1/2 ∧ ∀ i j, δ ≤ P i j := by
  let q : ι × ι → ℝ := fun ij => P ij.1 ij.2
  have hm : 0 < minCoord q := minCoord_pos (fun ij => hP ij.1 ij.2)
  refine ⟨min (minCoord q) (1/2), lt_min hm (by norm_num), min_le_right _ _, ?_⟩
  intro i j
  exact (min_le_left _ _).trans (minCoord_le q (i,j))

omit [Nonempty ι] in
lemma stochastic_lower_bound (p z : ι → ℝ) {δ L U : ℝ}
    (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1)
    (hδ : ∀ j, δ ≤ p j) (hz : ∀ j, L ≤ z j)
    (hmax : ∃ j, z j = U) :
    L + δ * (U-L) ≤ ∑ j, p j * z j := by
  classical
  obtain ⟨j,hj⟩ := hmax
  have hgap : 0 ≤ U-L := by rw [← hj]; exact sub_nonneg.mpr (hz j)
  have hterm : δ * (U-L) ≤ p j * (z j-L) := by
    rw [hj]
    exact mul_le_mul_of_nonneg_right (hδ j) hgap
  have hsum : p j * (z j-L) ≤ ∑ i, p i * (z i-L) :=
    Finset.single_le_sum (fun i _ => mul_nonneg (hp i) (sub_nonneg.mpr (hz i))) (Finset.mem_univ j)
  have he : (∑ i, p i * (z i-L)) = (∑ i, p i*z i)-L := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hs, one_mul]
  rw [he] at hsum
  linarith

lemma stochastic_coord_lower (p z : ι → ℝ) {δ : ℝ}
    (hp : ∀ j, 0 ≤ p j) (hs : ∑ j, p j = 1) (hδ : ∀ j, δ ≤ p j) :
    minCoord z + δ * (maxCoord z-minCoord z) ≤ ∑ j, p j*z j :=
  stochastic_lower_bound p z hp hs hδ (minCoord_le z) (exists_maxCoord z)

omit [Nonempty ι] in
lemma positive_weighted_sum (p z : ι → ℝ) (hp : ∀ j, 0 < p j)
    (hz : ∀ j, 0 ≤ z j) (hn : z ≠ 0) : 0 < ∑ j, p j*z j := by
  classical
  have he : ∃ j, 0 < z j := by
    by_contra h
    apply hn
    funext j
    have hj : ¬ 0 < z j := fun hj => h ⟨j,hj⟩
    exact le_antisymm (le_of_not_gt hj) (hz j)
  obtain ⟨j,hj⟩ := he
  exact (mul_pos (hp j) hj).trans_le
    (Finset.single_le_sum (fun i _ => mul_nonneg (hp i).le (hz i)) (Finset.mem_univ j))

end BellmanDP.Markovian.Fresh
end

section
open Finset
namespace BellmanDP.Markovian.Fresh
variable {N : ℕ} [Nonempty (Fin N)] {Q : Fin N → Type*}
variable {a : (i : Fin N) → Q i → Fin N → ℝ} {S : (i : Fin N) → Set (Q i)}
variable {m lam : ℝ} {y c : Fin N → ℝ}

lemma normalized_extrema_steps (h : MarkovHyp a S m) (hc : ∀ i, 0 ≤ c i)
    (hlam : 0 < lam) (hy : ∀ i, 0 < y i) (hey : IsMaxEigenpair a S lam y) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ n,
      minCoord (normalizedIter a S c lam y n) + δ *
        (maxCoord (normalizedIter a S c lam y n) - minCoord (normalizedIter a S c lam y n)) ≤
          minCoord (normalizedIter a S c lam y (n+1)) ∧
      maxCoord (normalizedIter a S c lam y (n+1)) ≤
        maxCoord (normalizedIter a S c lam y n) := by
  classical
  obtain ⟨qs,hqs,hsum⟩ := exists_stochastic_policy hey hlam hy
  let P : Fin N → Fin N → ℝ := fun i j => rowWeight a lam y i (qs i) j
  have hP : ∀ i j, 0 < P i j := fun i j => rowWeight_pos h hlam hy i (qs i) (hqs i) j
  obtain ⟨δ,hδ,hδ1,hδP⟩ := exists_positive_minorant P hP
  refine ⟨δ,hδ,by linarith,?_⟩
  intro n
  constructor
  · apply le_minCoord
    intro i
    have hlow := stochastic_coord_lower (P i) (normalizedIter a S c lam y n)
      (fun j => (hP i j).le) (hsum i) (hδP i)
    exact hlow.trans (normalized_row_le h hlam hy n i (qs i) (hqs i))
  · apply maxCoord_le
    intro i
    obtain ⟨q,hq,he⟩ := normalized_step_attained (c := c) h hlam hy n i
    rw [he]
    apply substochastic_upper
    · intro j
      exact (rowWeight_pos h hlam hy i q hq j).le
    · exact rowWeight_sum_le hey hlam hy i q hq
    · exact (le_minCoord (normalizedIter_nonneg h hc hlam hy n)).trans (minCoord_le_maxCoord _)
    · exact le_maxCoord _

end BellmanDP.Markovian.Fresh
end

section

noncomputable section
open Filter Topology
namespace BellmanDP.Markovian.Fresh

lemma positive_consensus_of_gap_contraction (l u : ℕ → ℝ) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (hlu : ∀ n, l n ≤ u n)
    (hlstep : ∀ n, l n + δ * (u n - l n) ≤ l (n + 1))
    (hustep : ∀ n, u (n + 1) ≤ u n) (hlpos : 0 < l 1) :
    ∃ α : ℝ, 0 < α ∧ Tendsto l atTop (𝓝 α) ∧ Tendsto u atTop (𝓝 α) := by
  have hlmono : Monotone l := by
    apply monotone_nat_of_le_succ
    intro n
    have hh := mul_nonneg hδ0.le (sub_nonneg.mpr (hlu n))
    linarith [hlstep n]
  have huanti : Antitone u := antitone_nat_of_succ_le hustep
  have hbounded : BddAbove (Set.range l) := by
    refine ⟨u 0, ?_⟩
    rintro x ⟨n, rfl⟩
    exact (hlu n).trans (huanti (Nat.zero_le n))
  let α := ⨆ n, l n
  have hl : Tendsto l atTop (𝓝 α) := tendsto_atTop_ciSup hlmono hbounded
  have hα : 0 < α := lt_of_lt_of_le hlpos (le_ciSup hbounded 1)
  let q := 1 - δ
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hstep : ∀ n, u (n + 1) - l (n + 1) ≤ q * (u n - l n) := by
    intro n
    dsimp [q]
    nlinarith [hlstep n, hustep n]
  have hbound : ∀ n, u n - l n ≤ (u 0 - l 0) * q ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          u (n + 1) - l (n + 1) ≤ q * (u n - l n) := hstep n
          _ ≤ q * ((u 0 - l 0) * q ^ n) := mul_le_mul_of_nonneg_left ih hq0
          _ = (u 0 - l 0) * q ^ (n + 1) := by rw [pow_succ]; ring
  have hpow : Tendsto (fun n : ℕ => q ^ n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
  have htop : Tendsto (fun n : ℕ => (u 0 - l 0) * q ^ n) atTop (𝓝 (0 : ℝ)) := by
    simpa using (tendsto_const_nhds.mul hpow)
  have hgap : Tendsto (fun n => u n - l n) atTop (𝓝 (0 : ℝ)) :=
    squeeze_zero (fun n => sub_nonneg.mpr (hlu n)) hbound htop
  refine ⟨α, hα, hl, ?_⟩
  have he : u = fun n => l n + (u n - l n) := by funext n; ring
  rw [he]
  simpa using hl.add hgap

end BellmanDP.Markovian.Fresh
end

section
open Filter Topology
namespace BellmanDP.Markovian.Fresh

theorem native_discrete_growth_asymptotics {N : ℕ} (hN : 0 < N) {Q : Fin N → Type*}
    (a : (i : Fin N) → Q i → Fin N → ℝ) (S : (i : Fin N) → Set (Q i)) (m : ℝ)
    (h : MarkovHyp a S m)
    (_huniq : ∃! qs, qs ∈ Set.pi Set.univ S ∧ ∀ q ∈ Set.pi Set.univ S,
      perronRoot (matOf a q) ≤ perronRoot (matOf a qs))
    (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i) (hc0 : c ≠ 0)
    (lam : ℝ) (y : Fin N → ℝ) (hlam : 0 < lam) (hy : ∀ i, 0 < y i)
    (hey : IsMaxEigenpair a S lam y) :
    ∃ α : ℝ, 0 < α ∧ ∀ i : Fin N,
      Tendsto (fun n : ℕ => maxIter a S c n i / lam ^ n) atTop (𝓝 (α * y i)) := by
  let : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  obtain ⟨δ,hδ0,hδ1,hstep⟩ := normalized_extrema_steps h hc hlam hy hey
  let z := normalizedIter a S c lam y
  have hlpos : 0 < minCoord (z 1) :=
    minCoord_pos (normalizedIter_one_pos h hc hc0 hlam hy)
  obtain ⟨α,hα,hl,hu⟩ := positive_consensus_of_gap_contraction
    (fun n => minCoord (z n)) (fun n => maxCoord (z n)) δ hδ0 hδ1
    (fun n => minCoord_le_maxCoord (z n)) (fun n => (hstep n).1)
    (fun n => (hstep n).2) hlpos
  refine ⟨α,hα,?_⟩
  intro i
  have hz : Tendsto (fun n => z n i) atTop (𝓝 α) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hl hu
      (fun n => minCoord_le (z n) i) (fun n => le_maxCoord (z n) i)
  have he : (fun n : ℕ => maxIter a S c n i / lam ^ n) =
      (fun n => z n i * y i) := by
    funext n
    dsimp [z,normalizedIter]
    have hyi := ne_of_gt (hy i)
    have hli := ne_of_gt hlam
    field_simp
  rw [he]
  exact hz.mul_const (y i)

end BellmanDP.Markovian.Fresh
end

open Filter Topology BellmanDP.Markovian

theorem solution {N : ℕ} (hN : 0 < N) {Q : Fin N → Type*}
    (a : (i : Fin N) → Q i → Fin N → ℝ) (S : (i : Fin N) → Set (Q i)) (m : ℝ)
    (h : MarkovHyp a S m)
    (huniq : ∃! qs, qs ∈ Set.pi Set.univ S ∧ ∀ q ∈ Set.pi Set.univ S,
      perronRoot (matOf a q) ≤ perronRoot (matOf a qs))
    (c : Fin N → ℝ) (hc : ∀ i, 0 ≤ c i) (hc0 : c ≠ 0)
    (lam : ℝ) (y : Fin N → ℝ) (hlam : 0 < lam) (hy : ∀ i, 0 < y i)
    (hey : IsMaxEigenpair a S lam y) :
    ∃ α : ℝ, 0 < α ∧ ∀ i : Fin N,
      Tendsto (fun n : ℕ => maxIter a S c n i / lam ^ n) atTop (𝓝 (α * y i))  := by
  exact Fresh.native_discrete_growth_asymptotics hN a S m h huniq c hc hc0 lam y hlam hy hey
