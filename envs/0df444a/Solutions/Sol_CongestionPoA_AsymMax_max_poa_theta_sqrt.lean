-- Prove2me | solution 1 for CongestionPoA.AsymMax.max_poa_theta_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-24T06:41:16.413563+00:00
-- url     : https://prove2.me/submissions/d349079a-53dd-4cb0-b7dc-2334cd677257

import Definitions.Def_CongestionPoA_AsymMax_Model
set_option autoImplicit false

set_option autoImplicit false
namespace CGProof

theorem integer_smoothness (x y : ℕ) :
    3 * (y : ℝ) * ((x : ℝ) + 1) ≤ (x : ℝ)^2 + 5 * (y : ℝ)^2 := by
  rcases Nat.eq_zero_or_pos y with rfl | hy
  · norm_num
  by_cases h : y = 1
  · subst y
    norm_num only [Nat.cast_one, one_pow, mul_one] at *
    by_cases hx : x ≤ 1
    · interval_cases x <;> norm_num
    · have hx : (2 : ℝ) ≤ x := by exact_mod_cast (by omega : 2 ≤ x)
      nlinarith [mul_nonneg (by linarith : 0 ≤ (x : ℝ)-1) (by linarith : 0 ≤ (x : ℝ)-2)]
  · have hy : (2 : ℝ) ≤ y := by exact_mod_cast (by omega : 2 ≤ y)
    nlinarith [sq_nonneg (2*(x : ℝ)-3*(y : ℝ)), mul_nonneg (by linarith : 0 ≤ (y : ℝ)) (by linarith : 0 ≤ 11*(y : ℝ)-12)]

theorem weighted_cauchy {E : Type*} (s : Finset E) (a x : E → ℝ)
    (ha : ∀ e ∈ s, 0 ≤ a e) :
    (∑ e ∈ s, a e*x e)^2 ≤ (∑ e ∈ s, a e)*(∑ e ∈ s, a e*x e^2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s ha
  · intro e he
    exact mul_nonneg (ha e he) (sq_nonneg _)
  · intro e _
    exact le_of_eq (by ring)

theorem cross_bound (D M t : ℝ) (hD : 0 ≤ D) (hM : 0 ≤ M)
    (ht : t^2 ≤ D*M^2) : t ≤ Real.sqrt D*M := by
  have hs := Real.sq_sqrt hD
  have hn := mul_nonneg (Real.sqrt_nonneg D) hM
  have he : (Real.sqrt D*M)^2 = D*M^2 := by rw [mul_pow, hs]
  nlinarith [sq_nonneg (t - Real.sqrt D*M)]
end CGProof

set_option autoImplicit false
open CongestionPoA.AsymMax
namespace CGProof
variable {I E J F : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
  [Fintype J] [DecidableEq J] [Fintype F] [DecidableEq F]

noncomputable def transportProfile (pi : I ≃ J) (phi : E ≃ F) (A : I → Finset E) : J → Finset F :=
  fun j => (A (pi.symm j)).map phi.toEmbedding

noncomputable def transportGame (pi : I ≃ J) (phi : E ≃ F) (G : CongestionGame I E) : CongestionGame J F where
  strategies j := (G.strategies (pi.symm j)).image (fun S => S.map phi.toEmbedding)
  latency f n := G.latency (phi.symm f) n

omit [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E] [Fintype J] [DecidableEq J] [Fintype F] [DecidableEq F] in
theorem transportProfile_apply (pi : I ≃ J) (phi : E ≃ F) (A : I → Finset E) (i : I) :
    transportProfile pi phi A (pi i) = (A i).map phi.toEmbedding := by simp [transportProfile]

omit [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E] [Fintype J] [DecidableEq J] [Fintype F] [DecidableEq F] in
theorem profile_roundtrip (pi : I ≃ J) (phi : E ≃ F) (A : I → Finset E) :
    transportProfile pi.symm phi.symm (transportProfile pi phi A) = A := by
  funext i
  ext e
  simp [transportProfile]

omit [DecidableEq I] [Fintype E] [DecidableEq J] [Fintype F] in
theorem transport_load (pi : I ≃ J) (phi : E ≃ F) (A : I → Finset E) (e : E) :
    load (transportProfile pi phi A) (phi e) = load A e := by
  unfold load
  exact (Finset.card_equiv pi (by intro i; simp [transportProfile])).symm

omit [DecidableEq I] [Fintype E] [DecidableEq J] [Fintype F] in
theorem transport_cost (pi : I ≃ J) (phi : E ≃ F) (G : CongestionGame I E)
    (A : I → Finset E) (i : I) :
    cost (transportGame pi phi G) (transportProfile pi phi A) (pi i) = cost G A i := by
  simp only [cost, transportProfile_apply, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro e _
  simp [transportGame, transport_load]

omit [Fintype I] [Fintype E] [DecidableEq E] [Fintype J] [Fintype F] [DecidableEq F] in
theorem transport_update (pi : I ≃ J) (phi : E ≃ F) (A : I → Finset E)
    (i : I) (S : Finset E) :
    transportProfile pi phi (Function.update A i S) =
      Function.update (transportProfile pi phi A) (pi i) (S.map phi.toEmbedding) := by
  funext j
  by_cases h : j = pi i
  · subst j; simp [transportProfile]
  · have hh : pi.symm j ≠ i := by intro he; apply h; simpa [he] using (pi.apply_symm_apply j).symm
    simp [transportProfile, h, hh]

omit [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E] [Fintype J] [DecidableEq J] [Fintype F] in
theorem transport_profile (pi : I ≃ J) (phi : E ≃ F) (G : CongestionGame I E)
    (A : I → Finset E) :
    IsProfile (transportGame pi phi G) (transportProfile pi phi A) ↔ IsProfile G A := by
  constructor
  · intro h i
    obtain ⟨S, hS, he⟩ := Finset.mem_image.mp (h (pi i))
    have he' : S = A i := by
      apply Finset.map_injective phi.toEmbedding
      simpa [transportProfile] using he
    simpa [he'] using hS
  · intro h j
    exact Finset.mem_image.mpr ⟨A (pi.symm j), h _, rfl⟩

omit [Fintype E] [Fintype F] in
theorem transport_nash (pi : I ≃ J) (phi : E ≃ F) (G : CongestionGame I E)
    (A : I → Finset E) :
    IsPureNash (transportGame pi phi G) (transportProfile pi phi A) ↔ IsPureNash G A := by
  constructor
  · rintro ⟨hp, hn⟩
    refine ⟨(transport_profile pi phi G A).mp hp, ?_⟩
    intro i S hS
    have hs : S.map phi.toEmbedding ∈ (transportGame pi phi G).strategies (pi i) := by
      exact Finset.mem_image.mpr ⟨S, by simpa using hS, rfl⟩
    have hh := hn (pi i) _ hs
    rw [← transport_update, transport_cost, transport_cost] at hh
    exact hh
  · rintro ⟨hp, hn⟩
    refine ⟨(transport_profile pi phi G A).mpr hp, ?_⟩
    intro j S hS
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    have hh := hn (pi.symm j) T hT
    rw [← transport_cost pi phi G A (pi.symm j),
      ← transport_cost pi phi G (Function.update A (pi.symm j) T) (pi.symm j)] at hh
    simpa only [transport_update, pi.apply_symm_apply] using hh


omit [DecidableEq I] [Fintype E] [DecidableEq J] [Fintype F] in
theorem transport_max [Nonempty I] [Nonempty J] (pi : I ≃ J) (phi : E ≃ F)
    (G : CongestionGame I E) (A : I → Finset E) :
    maxCost (transportGame pi phi G) (transportProfile pi phi A) = maxCost G A := by
  apply le_antisymm
  · apply Finset.sup'_le
    intro j _
    have hc := transport_cost pi phi G A (pi.symm j)
    simp only [pi.apply_symm_apply] at hc
    rw [hc]
    exact Finset.le_sup' _ (Finset.mem_univ _)
  · apply Finset.sup'_le
    intro i _
    rw [← transport_cost pi phi G A i]
    exact Finset.le_sup' _ (Finset.mem_univ _)

omit [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E] [Fintype J] [DecidableEq J] [Fintype F] in
theorem transport_linear (pi : I ≃ J) (phi : E ≃ F) (G : CongestionGame I E)
    (h : IsLinear G) : IsLinear (transportGame pi phi G) := by
  obtain ⟨a,b,ha,hb,h⟩ := h
  exact ⟨a ∘ phi.symm,b ∘ phi.symm,fun e => ha _,fun e => hb _,fun e n => h _ _⟩
end CGProof

set_option autoImplicit false
open Finset
open CongestionPoA.AsymMax
namespace CGProof
variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E]
omit [DecidableEq I] [Fintype E] in
lemma load_pos {A : I → Finset E} {i : I} {e : E} (h : e ∈ A i) :
    1 ≤ load A e := by
  exact Finset.card_pos.mpr ⟨i, by simp [h]⟩
omit [Fintype E] in
lemma load_update_le (A : I → Finset E) (i : I) (S : Finset E) (e : E) :
    load (Function.update A i S) e ≤ load A e + 1 := by
  unfold load
  calc
    _ ≤ ((univ.filter fun j => e ∈ A j) ∪ {i}).card := by
      apply card_le_card
      intro j hj
      by_cases hji : j = i
      · simp [hji]
      · simp only [mem_filter, mem_univ, true_and] at hj
        exact mem_union_left _ (by simpa [Function.update_of_ne hji] using hj)
    _ ≤ _ := by simpa using card_union_le (univ.filter fun j => e ∈ A j) {i}
omit [DecidableEq I] in
lemma incidence_sum (A : I → Finset E) (f : E → ℝ) :
    (∑ i, ∑ e ∈ A i, f e) = ∑ e, (load A e : ℝ) * f e := by
  calc
    _ = ∑ i, ∑ e, if e ∈ A i then f e else 0 := by simp
    _ = ∑ e, ∑ i, if e ∈ A i then f e else 0 := sum_comm
    _ = _ := by simp [load, ← sum_filter, nsmul_eq_mul]
omit [DecidableEq I] in
lemma sumCost_facility (G : CongestionGame I E) (A : I → Finset E) :
    sumCost G A = ∑ e, (load A e : ℝ) * G.latency e (load A e) :=
  incidence_sum A _
omit [DecidableEq I] [Fintype E] in
lemma cost_nonneg (G : CongestionGame I E) (hG : IsLinear G) (A : I → Finset E) (i : I) :
    0 ≤ cost G A i := by
  obtain ⟨a,b,ha,hb,h⟩ := hG
  exact sum_nonneg fun e _ => by rw [h]; exact add_nonneg (mul_nonneg (ha e) (Nat.cast_nonneg _)) (hb e)
omit [DecidableEq I] [Fintype E] in
lemma sumCost_nonneg (G : CongestionGame I E) (hG : IsLinear G) (A : I → Finset E) :
    0 ≤ sumCost G A := sum_nonneg fun i _ => cost_nonneg G hG A i
omit [DecidableEq I] [Fintype E] in
lemma cost_le_max [Nonempty I] (G : CongestionGame I E) (A : I → Finset E) (i : I) :
    cost G A i ≤ maxCost G A := le_sup' _ (mem_univ i)
omit [DecidableEq I] [Fintype E] in
lemma max_nonneg [Nonempty I] (G : CongestionGame I E) (hG : IsLinear G) (A : I → Finset E) :
    0 ≤ maxCost G A := (cost_nonneg G hG A (Classical.arbitrary I)).trans (cost_le_max G A _)
omit [DecidableEq I] [Fintype E] in
lemma sum_le_card_max [Nonempty I] (G : CongestionGame I E) (A : I → Finset E) :
    sumCost G A ≤ (Fintype.card I : ℝ) * maxCost G A := by
  calc
    _ ≤ ∑ i : I, maxCost G A := sum_le_sum fun i _ => cost_le_max G A i
    _ = _ := by simp
omit [Fintype E] in
lemma deviation (G : CongestionGame I E) (A P : I → Finset E)
    (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e)
    (hab : ∀ e n, G.latency e n = a e * n + b e)
    (hA : IsPureNash G A) (hP : IsProfile G P) (i : I) :
    cost G A i ≤ ∑ e ∈ P i, (a e * ((load A e : ℝ)+1) + b e) := by
  apply (hA.2 i (P i) (hP i)).trans
  simp only [cost, Function.update_self, hab]
  apply sum_le_sum
  intro e _
  have h := load_update_le A i (P i) e
  have hc : (load (Function.update A i (P i)) e : ℝ) ≤ (load A e : ℝ)+1 := by exact_mod_cast h
  exact add_le_add (mul_le_mul_of_nonneg_left hc (ha e)) le_rfl
omit [Fintype E] in
lemma cross_deviation (G : CongestionGame I E) (A P : I → Finset E)
    (a b : E → ℝ) (ha : ∀ e, 0 ≤ a e)
    (hab : ∀ e n, G.latency e n = a e * n + b e)
    (hA : IsPureNash G A) (hP : IsProfile G P) (i : I) :
    cost G A i ≤ cost G P i + ∑ e ∈ P i, a e * (load A e : ℝ) := by
  apply (deviation G A P a b ha hab hA hP i).trans
  simp only [cost, hab, ← sum_add_distrib]
  apply sum_le_sum
  intro e he
  have h : (1 : ℝ) ≤ load P e := by exact_mod_cast (load_pos (i:=i) he)
  nlinarith [mul_nonneg (ha e) (sub_nonneg.mpr h)]
omit [DecidableEq I] [Fintype E] in
lemma coeff_le_cost (G : CongestionGame I E) (P : I → Finset E)
    (a b : E → ℝ) (ha : ∀ e, 0≤a e) (hb : ∀ e, 0≤b e)
    (hab : ∀ e n, G.latency e n=a e*n+b e) (i : I) :
    (∑ e ∈ P i,a e) ≤ cost G P i := by
  apply sum_le_sum
  intro e he
  rw [hab]
  have h : (1:ℝ)≤load P e := by exact_mod_cast (load_pos (i:=i) he)
  nlinarith [mul_nonneg (ha e) (sub_nonneg.mpr h),hb e]
omit [DecidableEq I] in
lemma weighted_square_le_sum (G : CongestionGame I E) (A : I → Finset E)
    (a b : E → ℝ) (ha : ∀ e, 0≤a e) (hb : ∀ e, 0≤b e)
    (hab : ∀ e n, G.latency e n=a e*n+b e) (S : Finset E) :
    (∑ e ∈ S,a e*(load A e:ℝ)^2) ≤ sumCost G A := by
  rw [sumCost_facility]
  calc
    _ ≤ ∑ e,a e*(load A e:ℝ)^2 := sum_le_sum_of_subset_of_nonneg (subset_univ S) (by intro e _ _; exact mul_nonneg (ha e) (sq_nonneg _))
    _ ≤ _ := by
      apply sum_le_sum; intro e _; rw [hab]
      nlinarith [mul_nonneg (Nat.cast_nonneg (load A e) : (0:ℝ)≤load A e) (hb e)]
lemma total_bound (G : CongestionGame I E) (A P : I → Finset E)
    (a b : E → ℝ) (ha : ∀ e, 0≤a e) (hb : ∀ e, 0≤b e)
    (hab : ∀ e n, G.latency e n=a e*n+b e)
    (hA : IsPureNash G A) (hP : IsProfile G P) :
    sumCost G A ≤ (5/2:ℝ)*sumCost G P := by
  have hd : sumCost G A ≤ ∑ e,(load P e:ℝ)*(a e*((load A e:ℝ)+1)+b e) := by
    rw [← incidence_sum P]
    exact sum_le_sum fun i _ => deviation G A P a b ha hab hA hP i
  have he : 3*(∑ e,(load P e:ℝ)*(a e*((load A e:ℝ)+1)+b e)) ≤
      sumCost G A+5*sumCost G P := by
    rw [sumCost_facility,sumCost_facility, mul_sum,mul_sum,← sum_add_distrib]
    apply sum_le_sum
    intro e _
    rw [hab,hab]
    have hi := integer_smoothness (load A e) (load P e)
    have hh := mul_le_mul_of_nonneg_left hi (ha e)
    have hx : (0:ℝ)≤load A e := Nat.cast_nonneg _
    have hy : (0:ℝ)≤load P e := Nat.cast_nonneg _
    nlinarith [mul_nonneg (hb e) hx,mul_nonneg (hb e) hy]
  linarith
end CGProof

set_option autoImplicit false
open Finset CongestionPoA.AsymMax
namespace CGProof
variable {I E : Type*} [Fintype I] [DecidableEq I] [Fintype E] [DecidableEq E] [Nonempty I]
theorem upper_bound (G : CongestionGame I E) (A P : I → Finset E)
    (hG : IsLinear G) (hA : IsPureNash G A) (hP : IsProfile G P) :
    maxCost G A ≤ (1+Real.sqrt ((5/2:ℝ)*Fintype.card I))*maxCost G P := by
  obtain ⟨a,b,ha,hb,hab⟩ := hG
  have hG : IsLinear G := ⟨a,b,ha,hb,hab⟩
  have hM := max_nonneg G hG P
  have hT := sumCost_nonneg G hG A
  have ht := total_bound G A P a b ha hb hab hA hP
  have hsum := sum_le_card_max G P
  apply sup'_le
  intro i _
  have hdev := cross_deviation G A P a b ha hab hA hP i
  have hc := coeff_le_cost G P a b ha hb hab i
  have hci := cost_le_max G P i
  have hs := weighted_square_le_sum G A a b ha hb hab (P i)
  have hcoeff : 0 ≤ ∑ e ∈ P i,a e := sum_nonneg fun e _ => ha e
  have hsq := weighted_cauchy (P i) a (fun e => (load A e:ℝ)) (fun e _ => ha e)
  have hsq' : (∑ e ∈ P i,a e*(load A e:ℝ))^2 ≤
      ((5/2:ℝ)*Fintype.card I)*(maxCost G P)^2 := by
    calc
      _ ≤ (∑ e ∈ P i,a e)*sumCost G A := hsq.trans (mul_le_mul_of_nonneg_left hs hcoeff)
      _ ≤ maxCost G P*sumCost G A := mul_le_mul_of_nonneg_right (hc.trans hci) hT
      _ ≤ maxCost G P*((5/2:ℝ)*sumCost G P) := mul_le_mul_of_nonneg_left ht hM
      _ ≤ maxCost G P*((5/2:ℝ)*((Fintype.card I:ℝ)*maxCost G P)) := by gcongr
      _ = _ := by ring
  have hbnd := cross_bound ((5/2:ℝ)*Fintype.card I) (maxCost G P)
    (∑ e ∈ P i,a e*(load A e:ℝ)) (by positivity) hM hsq'
  nlinarith
end CGProof

set_option autoImplicit false
open Finset CongestionPoA.AsymMax
namespace CGProof
namespace Lower
abbrev Player (k : ℕ) := Option (Fin k × Fin (k-1))
abbrev Facility (k : ℕ) := Player k × Fin k
def block {k : ℕ} (i : Player k) : Finset (Facility k) :=
  univ.image fun t => (i,t)
@[simp] lemma mem_block {k : ℕ} (i : Player k) (e : Facility k) : e ∈ block i ↔ e.1=i := by
  simp [block, Prod.ext_iff, eq_comm]
@[simp] lemma card_block {k : ℕ} (i : Player k) : (block i).card=k := by
  rw [block, card_image_of_injective]
  · simp
  · intro a b h; exact (Prod.mk.inj h).2
noncomputable def game (k : ℕ) : CongestionGame (Player k) (Facility k) where
  strategies i := match i with
    | none => {block none}
    | some j => {block (some j), {(none,j.1)}}
  latency _ n := n
def P (k : ℕ) : Player k → Finset (Facility k) := block
def A (k : ℕ) : Player k → Finset (Facility k)
  | none => block none
  | some j => {(none,j.1)}
lemma linear (k : ℕ) : IsLinear (game k) := by
  exact ⟨fun _ => 1,fun _ => 0,by simp,by simp,by simp [game]⟩
lemma profileP (k : ℕ) : IsProfile (game k) (P k) := by
  intro i; cases i <;> simp [game,P]
lemma profileA (k : ℕ) : IsProfile (game k) (A k) := by
  intro i; cases i <;> simp [game,A]
lemma loadP (k : ℕ) (e : Facility k) : load (P k) e=1 := by
  unfold load
  have h : (univ.filter fun i => e ∈ P k i) = {e.1} := by ext i; simp [P,eq_comm]
  rw [h]; simp
lemma loadA (k : ℕ) (e : Facility k) :
    load (A k) e = if e.1=none then 1+(k-1) else 0 := by
  rcases e with ⟨i,t⟩
  cases i with
  | none =>
    rw [load, card_eq_sum_ones]
    simp only [sum_filter, Fintype.sum_option, Fintype.sum_prod_type]
    simp [A, Prod.ext_iff]
  | some j =>
    rw [load, card_eq_sum_ones]
    simp only [sum_filter, Fintype.sum_option, Fintype.sum_prod_type]
    simp [A]
lemma costP (k : ℕ) (i : Player k) : cost (game k) (P k) i=(k:ℝ) := by
  simp only [cost, game, loadP]
  simp [P]
lemma costA_none (k : ℕ) (hk : 1≤k) : cost (game k) (A k) none=(k:ℝ)^2 := by
  have h : 1+(k-1)=k := by omega
  simp only [cost,game,A,loadA,h]
  calc
    _ = ∑ _e ∈ block (none : Player k), (k:ℝ) := by
      apply sum_congr rfl; intro e he; rw [if_pos ((mem_block none e).mp he)]
    _ = _ := by simp [sq]
lemma costA_some (k : ℕ) (hk : 1≤k) (j : Fin k × Fin (k-1)) :
    cost (game k) (A k) (some j)=(k:ℝ) := by
  have h : 1+(k-1)=k := by omega
  simp [cost,game,A,loadA,h]
lemma private_update_load (k : ℕ) (j : Fin k × Fin (k-1)) (e : Facility k)
    (he : e ∈ block (some j)) : load (Function.update (A k) (some j) (block (some j))) e=1 := by
  have hep := (mem_block (some j) e).mp he
  have hn : ∀ i, e ∉ A k i := by
    intro i
    cases i with
    | none => simp [A,hep]
    | some q => simp [A,Prod.ext_iff,hep]
  unfold load
  have h : (univ.filter fun i => e ∈ Function.update (A k) (some j) (block (some j)) i) = {some j} := by
    ext i
    by_cases hi : i=some j
    · simp [hi,he]
    · simp [hi,hn]
  rw [h]; simp
lemma private_deviation_cost (k : ℕ) (j : Fin k × Fin (k-1)) :
    cost (game k) (Function.update (A k) (some j) (block (some j))) (some j) = (k:ℝ) := by
  simp only [cost,Function.update_self,game]
  calc
    _ = ∑ _e ∈ block (some j), (1:ℝ) := by
      apply sum_congr rfl; intro e he; rw [private_update_load k j e he]; norm_num
    _ = _ := by simp
lemma nash (k : ℕ) (hk : 1≤k) : IsPureNash (game k) (A k) := by
  refine ⟨profileA k,?_⟩
  intro i S hS
  cases i with
  | none =>
    have hs : S=block none := by simpa [game] using hS
    subst S
    have he : Function.update (A k) none (block none)=A k := by
      simpa only [A] using Function.update_eq_self none (A k)
    rw [he]
  | some j =>
    have hs : S=block (some j) ∨ S={(none,j.1)} := by simpa [game] using hS
    rcases hs with rfl|rfl
    · rw [costA_some k hk j,private_deviation_cost]
    · have he : Function.update (A k) (some j) {(none,j.1)}=A k := by
        simpa only [A] using Function.update_eq_self (some j) (A k)
      rw [he]
lemma maxP (k : ℕ) : maxCost (game k) (P k)=(k:ℝ) := by
  exact sup'_eq_of_forall univ_nonempty _ (fun i _ => costP k i)
lemma maxA (k : ℕ) (hk : 1≤k) : maxCost (game k) (A k)=(k:ℝ)^2 := by
  apply le_antisymm
  · apply sup'_le; intro i _
    cases i with
    | none => rw [costA_none k hk]
    | some j =>
      rw [costA_some k hk j]
      have h : (1:ℝ)≤k := by exact_mod_cast hk
      nlinarith
  · rw [← costA_none k hk]
    exact le_sup' _ (mem_univ none)
lemma optimal (k : ℕ) (Q : Player k → Finset (Facility k)) (hQ : IsProfile (game k) Q) :
    (k:ℝ)≤ maxCost (game k) Q := by
  have hnone : Q none=block none := by simpa [game] using hQ none
  have hl : (k:ℝ)≤cost (game k) Q none := by
    simp only [cost,game,hnone]
    calc
      _ = ∑ _e ∈ block (none : Player k), (1:ℝ) := by simp
      _ ≤ _ := by
        apply sum_le_sum;intro e he
        have h : 1≤load Q e := Finset.card_pos.mpr ⟨none,by simp [hnone,he]⟩
        exact_mod_cast h
  exact hl.trans (le_sup' _ (mem_univ none))
end Lower
theorem lower_bound (k : ℕ) (hk : 2≤k)
    [Nonempty (Fin (k*(k-1)+1))] :
    ∃ (G : CongestionGame (Fin (k*(k-1)+1)) (Fin (k*(k*(k-1)+1))))
      (A P : Fin (k*(k-1)+1) → Finset (Fin (k*(k*(k-1)+1)))),
      IsLinear G ∧ (∀ e n,G.latency e n=(n:ℝ)) ∧ IsPureNash G A ∧ IsProfile G P ∧
      maxCost G A=(k:ℝ)^2 ∧ maxCost G P=(k:ℝ) ∧
      (∀ Q,IsProfile G Q → (k:ℝ) ≤ maxCost G Q) := by
  classical
  have hj : Fintype.card (Lower.Player k)=k*(k-1)+1 := by simp [Lower.Player]
  have he : Fintype.card (Lower.Facility k)=k*(k*(k-1)+1) := by
    simp [Lower.Facility,hj,mul_comm]
  let pi := Fintype.equivFinOfCardEq hj
  let phi := Fintype.equivFinOfCardEq he
  let G := transportGame pi phi (Lower.game k)
  refine ⟨G,transportProfile pi phi (Lower.A k),transportProfile pi phi (Lower.P k),
    transport_linear pi phi _ (Lower.linear k),?_,
    (transport_nash pi phi _ _).mpr (Lower.nash k (by omega)),
    (transport_profile pi phi _ _).mpr (Lower.profileP k),?_,?_,?_⟩
  · intro e n; rfl
  · rw [transport_max]; exact Lower.maxA k (by omega)
  · rw [transport_max]; exact Lower.maxP k
  · intro Q hQ
    let Q0 := transportProfile pi.symm phi.symm Q
    have hround : transportProfile pi phi Q0=Q := profile_roundtrip pi.symm phi.symm Q
    have hp : IsProfile (Lower.game k) Q0 := by
      apply (transport_profile pi phi _ _).mp
      simpa only [hround] using hQ
    have hm := transport_max pi phi (Lower.game k) Q0
    rw [hround] at hm
    rw [hm]
    exact Lower.optimal k Q0 hp
end CGProof

set_option autoImplicit false
namespace CongestionPoA.AsymMax

/-- Christodoulou and Koutsoupias, STOC 2005, Theorems 5 and 6,
PDF pp. 4–5. The pure maximum-cost price of anarchy has order `√N`.
Formalization Note: the first clause is the proof's explicit upper bound for
every feasible comparison profile. The second fixes `N = k(k−1)+1` and
`kN` facilities with identity latencies, exact positive costs `k²`, `k`, and
optimality of the comparison profile.
It records the corrected denominator `k−1` implicit in Figure 2; the
paper's printed `k` makes the proposed profile fail to be Nash. The
network realization mentioned in Theorem 6 is not encoded. -/
theorem max_poa_theta_sqrt :
    (∀ (N : ℕ) (hN : 1 ≤ N),
      letI : Nonempty (Fin N) := ⟨⟨0, Nat.zero_lt_of_lt hN⟩⟩
      ∀ (E : Type) [Fintype E] [DecidableEq E]
        (G : CongestionGame (Fin N) E) (A P : Fin N → Finset E),
        IsLinear G → IsPureNash G A → IsProfile G P →
          maxCost G A ≤ (1 + Real.sqrt ((5 / 2 : ℝ) * N)) * maxCost G P) ∧
    (∀ (k : ℕ) (_hk : 2 ≤ k),
      let N := k * (k - 1) + 1
      letI : Nonempty (Fin N) := ⟨⟨0, Nat.succ_pos _⟩⟩
      ∃ (G : CongestionGame (Fin N) (Fin (k * N)))
        (A P : Fin N → Finset (Fin (k * N))),
        IsLinear G ∧
        (∀ e n, G.latency e n = (n : ℝ)) ∧
        IsPureNash G A ∧ IsProfile G P ∧
        maxCost G A = (k : ℝ) ^ 2 ∧ maxCost G P = (k : ℝ) ∧
        (∀ Q, IsProfile G Q → (k : ℝ) ≤ maxCost G Q)) := by
  constructor
  · intro N hN
    let : Nonempty (Fin N) := ⟨⟨0, Nat.zero_lt_of_lt hN⟩⟩
    intro E _ _ G A P hG hA hP
    simpa only [Fintype.card_fin] using CGProof.upper_bound G A P hG hA hP
  · intro k hk
    let : Nonempty (Fin (k*(k-1)+1)) := ⟨⟨0, Nat.succ_pos _⟩⟩
    exact CGProof.lower_bound k hk


end CongestionPoA.AsymMax

open CongestionPoA.AsymMax
theorem solution :
    (∀ (N : ℕ) (hN : 1 ≤ N),
      letI : Nonempty (Fin N) := ⟨⟨0, Nat.zero_lt_of_lt hN⟩⟩
      ∀ (E : Type) [Fintype E] [DecidableEq E]
        (G : CongestionGame (Fin N) E) (A P : Fin N → Finset E),
        IsLinear G → IsPureNash G A → IsProfile G P →
          maxCost G A ≤ (1 + Real.sqrt ((5 / 2 : ℝ) * N)) * maxCost G P) ∧
    (∀ (k : ℕ) (_hk : 2 ≤ k),
      let N := k * (k - 1) + 1
      letI : Nonempty (Fin N) := ⟨⟨0, Nat.succ_pos _⟩⟩
      ∃ (G : CongestionGame (Fin N) (Fin (k * N)))
        (A P : Fin N → Finset (Fin (k * N))),
        IsLinear G ∧
        (∀ e n, G.latency e n = (n : ℝ)) ∧
        IsPureNash G A ∧ IsProfile G P ∧
        maxCost G A = (k : ℝ) ^ 2 ∧ maxCost G P = (k : ℝ) ∧
        (∀ Q, IsProfile G Q → (k : ℝ) ≤ maxCost G Q)) := CongestionPoA.AsymMax.max_poa_theta_sqrt
