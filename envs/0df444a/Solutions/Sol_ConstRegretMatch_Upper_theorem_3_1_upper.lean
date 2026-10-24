-- Prove2me | solution 1 for ConstRegretMatch.Upper.theorem_3_1_upper
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T23:17:33.161492+00:00
-- url     : https://prove2.me/submissions/73f06d8e-f86f-4722-8d5f-66d4ba6c6051
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_ConstRegretMatch_Upper_Network
import Definitions.Def_ConstRegretMatch_Upper_SPP
import Definitions.Def_ConstRegretMatch_Upper_Arrivals
import Definitions.Def_ConstRegretMatch_Upper_Policy
import Definitions.Def_ConstRegretMatch_Upper_Resolving
import Theorems.Thm_ConstRegretMatch_Upper_dual_theta
import Theorems.Thm_ConstRegretMatch_Upper_lemma_4_1
import Theorems.Thm_ConstRegretMatch_Upper_appD_epoch_hstar

open ConstRegretMatch.Upper

namespace CRMT31Sol

variable {n d : ℕ}

/-! ### Expectations -/

lemma expect_mono (lam : Fin n → ℝ) (hlam : IsArrivalRates lam) (t : ℕ)
    (F G : (ℕ → Fin n) → ℝ) (h : ∀ ω, F ω ≤ G ω) : expect lam t F ≤ expect lam t G := by
  unfold expect
  split_ifs with hn
  · apply Finset.sum_le_sum
    intro w _
    apply mul_le_mul_of_nonneg_left (h _)
    exact Finset.prod_nonneg (fun s _ => (hlam.1 _).le)
  · exact le_refl _

lemma expect_add (lam : Fin n → ℝ) (t : ℕ) (F G : (ℕ → Fin n) → ℝ) :
    expect lam t (fun ω => F ω + G ω) = expect lam t F + expect lam t G := by
  unfold expect
  split_ifs
  · rw [← Finset.sum_add_distrib]; apply Finset.sum_congr rfl; intro w _; ring
  · simp

lemma expect_const_mul (lam : Fin n → ℝ) (t : ℕ) (c : ℝ) (F : (ℕ → Fin n) → ℝ) :
    expect lam t (fun ω => c * F ω) = c * expect lam t F := by
  unfold expect
  split_ifs
  · rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro w _; ring
  · simp

lemma expect_succ (lam : Fin n → ℝ) (hlam : IsArrivalRates lam) (t : ℕ)
    (G : (ℕ → Fin n) → ℝ) (hG : ∀ ω ω', (∀ s < t, ω s = ω' s) → G ω = G ω') :
    expect lam (t + 1) G = expect lam t G := by
  unfold expect
  split_ifs with hn
  · rw [← (Fin.snocEquiv (fun _ => Fin n)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w' _
    have hext : ∀ a, G (extendPath ((Fin.snocEquiv (fun _ => Fin n)) (a, w')) ⟨0, hn⟩) =
        G (extendPath w' ⟨0, hn⟩) := by
      intro a
      apply hG
      intro s hs
      have hs1 : s < t + 1 := by omega
      simp only [extendPath, hs, hs1, dif_pos, Fin.snocEquiv_apply]
      have : (⟨s, hs1⟩ : Fin (t + 1)) = Fin.castSucc ⟨s, hs⟩ := rfl
      rw [this, Fin.snoc_castSucc]
    simp_rw [hext, Fin.prod_univ_castSucc, Fin.snocEquiv_apply, Fin.snoc_castSucc, Fin.snoc_last]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hlam.2]
    ring
  · rfl

lemma expect_ge (lam : Fin n → ℝ) (hlam : IsArrivalRates lam) (a : ℕ)
    (G : (ℕ → Fin n) → ℝ) (hG : ∀ ω ω', (∀ s < a, ω s = ω' s) → G ω = G ω') :
    ∀ b, a ≤ b → expect lam b G = expect lam a G := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
    rw [expect_succ lam hlam b G (fun ω ω' h => hG ω ω' (fun s hs => h s (by omega))), ih]

lemma expect_const (lam : Fin n → ℝ) (hlam : IsArrivalRates lam) (t : ℕ) (c : ℝ) :
    expect lam t (fun _ => c) = c := by
  rw [expect_ge lam hlam 0 _ (fun _ _ _ => rfl) t (Nat.zero_le t)]
  unfold expect
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; have := hlam.2; simp at this
    · exact h
  rw [dif_pos hn]
  simp

/-! ### Arrivals -/

lemma arrivals_mono (ω : ℕ → Fin n) {s t : ℕ} (h : t ≤ s) (i : Fin n) :
    arrivals ω t i ≤ arrivals ω s i := by
  unfold arrivals arrivalsBetween
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.Ico_subset_Ico_right h

lemma arrivals_add (ω : ℕ → Fin n) {a b : ℕ} (h : a ≤ b) (i : Fin n) :
    arrivals ω b i = arrivals ω a i + arrivalsBetween ω a b i := by
  unfold arrivals arrivalsBetween
  rw [← Finset.Ico_union_Ico_eq_Ico (Nat.zero_le a) h, Finset.filter_union,
    Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive 0 a b)

lemma between_le (ω : ℕ → Fin n) (a b : ℕ) (i : Fin n) : arrivalsBetween ω a b i ≤ b - a := by
  unfold arrivalsBetween
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma between_congr (ω ω' : ℕ → Fin n) (a b : ℕ) (h : ∀ s < b, ω s = ω' s) :
    arrivalsBetween ω a b = arrivalsBetween ω' a b := by
  funext i
  unfold arrivalsBetween
  congr 1
  apply Finset.filter_congr
  intro x hx
  rw [Finset.mem_Ico] at hx
  rw [h x hx.2]

/-! ### The resolving policy -/

section policy

variable (N : MatchingNetwork n d) (sel : (Fin n → ℕ) → Fin d → ℕ) (Qp : Finset (Fin n))
  (τ : ℕ)

lemma epochQueue_congr : ∀ k (ω ω' : ℕ → Fin n), (∀ s < k * τ, ω s = ω' s) →
    epochQueue N sel Qp τ k ω = epochQueue N sel Qp τ k ω' := by
  intro k
  induction k with
  | zero => intro ω ω' _; rfl
  | succ k ih =>
    intro ω ω' h
    have h1 : ∀ s < k * τ, ω s = ω' s := fun s hs =>
      h s (lt_of_lt_of_le hs (Nat.mul_le_mul_right τ (Nat.le_succ k)))
    funext i
    simp only [epochQueue]
    rw [ih ω ω' h1, between_congr ω ω' _ _ h]

/-- cumulative matched agents of type `i` after `k` epochs -/
def T (k : ℕ) (ω : ℕ → Fin n) (i : Fin n) : ℕ :=
  ∑ m, N.inc i m * ∑ k' ∈ Finset.Icc 1 k, sel (epochQueue N sel Qp τ k' ω) m

lemma postMatch_zero : postMatch N sel Qp 0 = 0 := by
  funext i; simp [postMatch]

lemma T_succ (k : ℕ) (ω : ℕ → Fin n) (i : Fin n) :
    T N sel Qp τ (k + 1) ω i = T N sel Qp τ k ω i +
      ∑ m, N.inc i m * sel (epochQueue N sel Qp τ (k + 1) ω) m := by
  unfold T
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  rw [Finset.sum_Icc_succ_top (by omega), mul_add]

lemma invariant (hsel : ∀ u, StaticFeasible N u (sel u)) (ω : ℕ → Fin n) :
    ∀ k i, T N sel Qp τ k ω i + postMatch N sel Qp (epochQueue N sel Qp τ k ω) i
        ≤ arrivals ω (k * τ) i ∧
      (i ∉ Qp → T N sel Qp τ k ω i + postMatch N sel Qp (epochQueue N sel Qp τ k ω) i
        = arrivals ω (k * τ) i) := by
  intro k
  induction k with
  | zero =>
    intro i
    simp [T, epochQueue, postMatch, arrivals, arrivalsBetween]
  | succ k ih =>
    intro i
    obtain ⟨ih1, ih2⟩ := ih i
    rw [T_succ]
    have hadd := arrivals_add ω (show k * τ ≤ (k + 1) * τ from Nat.mul_le_mul_right τ (by omega)) i
    set q := epochQueue N sel Qp τ (k + 1) ω with hq
    have hqi : q i = postMatch N sel Qp (epochQueue N sel Qp τ k ω) i +
        arrivalsBetween ω (k * τ) ((k + 1) * τ) i := by
      rw [hq]; rfl
    have hf := hsel q i
    unfold StaticFeasible at hf
    set sv := ∑ m, N.inc i m * sel q m
    unfold postMatch
    by_cases hi : i ∈ Qp
    · simp only [hi, if_true, add_zero, not_true_eq_false, IsEmpty.forall_iff, and_true]
      have : (k + 1) * τ = k * τ + τ := by ring
      omega
    · simp only [hi, if_false, not_false_eq_true, forall_const]
      have e := ih2 hi
      constructor <;> omega

lemma T_le (hsel : ∀ u, StaticFeasible N u (sel u)) (ω : ℕ → Fin n) (k : ℕ) (i : Fin n) :
    T N sel Qp τ k ω i ≤ arrivals ω (k * τ) i :=
  le_trans (Nat.le_add_right _ _) (invariant N sel Qp τ hsel ω k i).1

lemma inc_D (t : ℕ) (ω : ℕ → Fin n) (i : Fin n) :
    ∑ m, N.inc i m * resolvingPolicy N sel Qp τ t ω m = T N sel Qp τ (t / τ) ω i := rfl

lemma admissible (hsel : ∀ u, StaticFeasible N u (sel u)) :
    IsAdmissible N (resolvingPolicy N sel Qp τ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω; funext m; simp [resolvingPolicy]
  · intro t ω m
    unfold resolvingPolicy
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · apply Finset.Icc_subset_Icc (le_refl 1)
      exact Nat.div_le_div_right (Nat.le_succ t)
    · intro _ _ _; exact Nat.zero_le _
  · intro t ω ω' h
    funext m
    unfold resolvingPolicy
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.mem_Icc] at hk
    rw [epochQueue_congr N sel Qp τ k ω ω' (fun s hs => h s (lt_of_lt_of_le hs
      ((Nat.mul_le_mul_right τ hk.2).trans (Nat.div_mul_le_self t τ))))]
  · intro t ω i
    rw [inc_D]
    exact (T_le N sel Qp τ hsel ω _ i).trans (arrivals_mono ω (Nat.div_mul_le_self t τ) i)

/-- For a type outside `Qp`, the queue at time `t ≥ 1` is the post-match queue of the last epoch
plus at most `τ` new arrivals. -/
lemma queue_le (hsel : ∀ u, StaticFeasible N u (sel u)) (hτ : 1 ≤ τ) (ω : ℕ → Fin n) (t : ℕ)
    (ht : 1 ≤ t) (i : Fin n) (hi : i ∉ Qp) :
    queue N (resolvingPolicy N sel Qp τ) ω t i ≤
      postMatch N sel Qp (epochQueue N sel Qp τ ((t - 1) / τ) ω) i + τ := by
  unfold queue
  rw [inc_D]
  set k := (t - 1) / τ
  have e := (invariant N sel Qp τ hsel ω k i).2 hi
  have hkt : k * τ ≤ t := (Nat.div_mul_le_self (t - 1) τ).trans (by omega)
  have hadd := arrivals_add ω hkt i
  have hb := between_le ω (k * τ) t i
  have hlt : t - 1 < k * τ + τ := by
    have := Nat.lt_div_mul_add (a := t - 1) (show 0 < τ by omega)
    simpa [k] using this
  omega

end policy

/-! ### h* and the dual vector -/

lemma post_le_hstar (N : MatchingNetwork n d) (r : Fin d → ℝ) (z : Fin d → ℝ) (s : Fin n → ℝ)
    (θ : Fin n → ℝ) (hθd : IsSPPDual N r z s θ) (hθ0 : ∀ i, 0 ≤ θ i)
    (sel : (Fin n → ℕ) → Fin d → ℕ) (hsel : IsResolvingSelection N r (Mzero z) sel)
    (u : Fin n → ℕ) (i : Fin n) (hi : i ∈ Qzero s) :
    θ i * (postMatch N sel (Qplus s) u i : ℝ) ≤ hstar N z s θ u := by
  classical
  set val : (Fin d → ℕ) → ℝ := fun y =>
    ∑ j ∈ Qzero s, θ j * ((u j : ℝ) - ∑ m, N.M j m * (y m : ℝ)) with hval
  have hQ : ∀ j, j ∈ Qzero s ↔ j ∉ Qplus s := by
    intro j; simp [Qzero, Qplus]
  have key : ∀ y : Fin d → ℕ, (∀ m ∈ Mzero z, y m = 0) →
      val y = ∑ j ∈ Qzero s, θ j * (u j : ℝ) - ∑ m, r m * (y m : ℝ) := by
    intro y hy
    simp only [hval, mul_sub, Finset.sum_sub_distrib]
    congr 1
    have h1 : ∑ j ∈ Qzero s, θ j * ∑ m, N.M j m * (y m : ℝ) =
        ∑ j, θ j * ∑ m, N.M j m * (y m : ℝ) := by
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ hj
      rw [hQ, not_not] at hj
      rw [hθd.1 j hj, zero_mul]
    rw [h1]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hm : m ∈ Mplus z
    · rw [← hθd.2 m hm, Finset.sum_mul]
      apply Finset.sum_congr rfl; intro j _; ring
    · have : m ∈ Mzero z := by simpa [Mplus, Mzero] using hm
      rw [hy m this]; simp
  have hselv : ∀ y : Fin d → ℕ, StaticFeasible N u y → (∀ m ∈ Mzero z, y m = 0) →
      val (sel u) ≤ val y := by
    intro y hy1 hy2
    rw [key y hy2, key (sel u) (hsel u).2.1]
    have := (hsel u).2.2 y hy1 hy2
    linarith
  have hmin : val (sel u) ≤ hstar N z s θ u := by
    unfold hstar
    apply Finset.le_min'
    intro x hx
    rw [Finset.mem_insert, Finset.mem_image] at hx
    rcases hx with rfl | ⟨y, hy, rfl⟩
    · have h0 := hselv 0 (fun j => by simp) (fun m _ => rfl)
      simpa [hval] using h0
    · rw [Finset.mem_filter] at hy
      exact hselv y hy.2.1 hy.2.2
  have hpost : ∀ j ∈ Qzero s, (postMatch N sel (Qplus s) u j : ℝ) =
      (u j : ℝ) - ∑ m, N.M j m * (sel u m : ℝ) := by
    intro j hj
    have hj' := (hQ j).1 hj
    have hf := (hsel u).1 j
    simp only [postMatch, hj', if_false]
    rw [Nat.cast_sub hf]
    push_cast
    simp [MatchingNetwork.M]
  have hsum : θ i * (postMatch N sel (Qplus s) u i : ℝ) ≤
      ∑ j ∈ Qzero s, θ j * (postMatch N sel (Qplus s) u j : ℝ) :=
    Finset.single_le_sum (f := fun j => θ j * (postMatch N sel (Qplus s) u j : ℝ))
      (fun j _ => mul_nonneg (hθ0 j) (Nat.cast_nonneg _)) hi
  have heq : ∑ j ∈ Qzero s, θ j * (postMatch N sel (Qplus s) u j : ℝ) = val (sel u) := by
    simp only [hval]
    apply Finset.sum_congr rfl
    intro j hj
    rw [hpost j hj]
  linarith

/-- `Good P Q i`: the complementary-slackness system of the basis `(P, Q)` has a solution that is
positive off `Q`, and `i ∉ Q`. -/
def Good (N : MatchingNetwork n d) (r : Fin d → ℝ) (P : Finset (Fin d)) (Q : Finset (Fin n))
    (i : Fin n) : Prop :=
  i ∉ Q ∧ ∃ θ : Fin n → ℝ, ((∀ j ∈ Q, θ j = 0) ∧ ∀ m ∈ P, ∑ k, N.M k m * θ k = r m) ∧
    ∀ j, j ∉ Q → 0 < θ j

open Classical in
noncomputable def vval (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (x : Finset (Fin d) × Finset (Fin n) × Fin n) : ℝ :=
  if h : Good N r x.1 x.2.1 x.2.2 then (Classical.choose h.2) x.2.2 else 1

lemma vval_pos (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (x : Finset (Fin d) × Finset (Fin n) × Fin n) : 0 < vval N r x := by
  unfold vval
  split_ifs with h
  · exact (Classical.choose_spec h.2).2 _ h.1
  · exact one_pos

open Classical in
noncomputable def thmin (N : MatchingNetwork n d) (r : Fin d → ℝ) : ℝ :=
  (insert 1 (Finset.univ.image (vval N r))).min' (Finset.insert_nonempty _ _)

lemma thmin_pos (N : MatchingNetwork n d) (r : Fin d → ℝ) : 0 < thmin N r := by
  classical
  unfold thmin
  rw [Finset.lt_min'_iff]
  intro y hy
  rw [Finset.mem_insert, Finset.mem_image] at hy
  rcases hy with rfl | ⟨x, _, rfl⟩
  · exact one_pos
  · exact vval_pos N r x

lemma theta_ge (N : MatchingNetwork n d) (r : Fin d → ℝ) (z : Fin d → ℝ) (s : Fin n → ℝ)
    (θ : Fin n → ℝ) (hθ : IsSPPDual N r z s θ)
    (huniq : ∀ θ', IsSPPDual N r z s θ' → θ' = θ) (hpos : ∀ i ∈ Qzero s, 0 < θ i)
    (i : Fin n) (hi : i ∈ Qzero s) : thmin N r ≤ θ i := by
  classical
  have hQ : ∀ j, j ∈ Qzero s ↔ j ∉ Qplus s := by
    intro j; simp [Qzero, Qplus]
  have hg : Good N r (Mplus z) (Qplus s) i :=
    ⟨(hQ i).1 hi, θ, hθ, fun j hj => hpos j ((hQ j).2 hj)⟩
  have hv : vval N r (Mplus z, Qplus s, i) = θ i := by
    unfold vval
    rw [dif_pos hg]
    have := huniq _ (Classical.choose_spec hg.2).1
    rw [this]
  rw [← hv]
  unfold thmin
  apply Finset.min'_le
  exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _))

/-! ### The gap -/

lemma gap_facts (N : MatchingNetwork n d) (r : Fin d → ℝ) (lam : Fin n → ℝ)
    (hlam : IsArrivalRates lam) (z : Fin d → ℝ) (s : Fin n → ℝ) (hGP : IsGP N r lam z s) :
    0 < gpGap z s ∧ gpGap z s ≤ 1 := by
  classical
  obtain ⟨⟨hz0, hs0, hfeas⟩, _⟩ := hGP.1
  have hn : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; have := hlam.2; simp at this
    · exact h
  have hlam1 : ∀ i, lam i ≤ 1 := by
    intro i
    rw [← hlam.2]
    exact Finset.single_le_sum (fun j _ => (hlam.1 j).le) (Finset.mem_univ i)
  have hne : (gapValues z s).Nonempty := by
    have hc := hGP.2.2
    by_cases hM : (Mplus z).Nonempty
    · exact (hM.image z).mono Finset.subset_union_left
    · have hM0 : (Mplus z).card = 0 := by
        rw [Finset.card_eq_zero]; exact Finset.not_nonempty_iff_eq_empty.mp hM
      have hQ : (Qplus s).Nonempty := by
        rw [← Finset.card_pos]; omega
      exact (hQ.image s).mono Finset.subset_union_right
  have hel : ∀ x ∈ gapValues z s, 0 < x ∧ x ≤ 1 := by
    intro x hx
    simp only [gapValues, Finset.mem_union, Finset.mem_image, Mplus, Qplus, Finset.mem_filter,
      Finset.mem_univ, true_and] at hx
    rcases hx with ⟨m, hm, rfl⟩ | ⟨j, hj, rfl⟩
    · refine ⟨hm, ?_⟩
      obtain ⟨i, hi⟩ : (N.A m).Nonempty := by
        have := N.two_le_card m
        exact Finset.card_pos.mp (by omega)
      have h1 : N.M i m * z m ≤ ∑ m', N.M i m' * z m' :=
        Finset.single_le_sum (f := fun m' => N.M i m' * z m')
          (fun m' _ => mul_nonneg (by simp [MatchingNetwork.M]) (hz0 m')) (Finset.mem_univ m)
      have h2 : N.M i m = 1 := by simp [MatchingNetwork.M, MatchingNetwork.inc, hi]
      rw [h2, one_mul] at h1
      have := hfeas i
      linarith [hs0 i, hlam1 i]
    · refine ⟨hj, ?_⟩
      have h1 : 0 ≤ ∑ m', N.M j m' * z m' :=
        Finset.sum_nonneg (fun m' _ => mul_nonneg (by simp [MatchingNetwork.M]) (hz0 m'))
      have := hfeas j
      linarith [hlam1 j]
  unfold gpGap
  rw [dif_pos hne]
  exact hel _ (Finset.min'_mem _ _)

end CRMT31Sol

open CRMT31Sol in
theorem solution {n d : ℕ} (N : MatchingNetwork n d) (r : Fin d → ℝ)
    (hr : IsMatchValues r) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ Γ : ℝ, 0 < Γ ∧
      ∀ (lam : Fin n → ℝ), IsArrivalRates lam →
      ∀ (z : Fin d → ℝ) (s : Fin n → ℝ), IsGP N r lam z s →
      ∀ sel : (Fin n → ℕ) → Fin d → ℕ, IsResolvingSelection N r (Mzero z) sel →
        IsAdmissible N (resolvingPolicy N sel (Qplus s) ⌈κ / gpGap z s⌉₊) ∧
        ∀ t : ℕ, 1 ≤ t →
          Rstar N lam r t - valueOf lam r (resolvingPolicy N sel (Qplus s) ⌈κ / gpGap z s⌉₊) t
            ≤ Γ / gpGap z s := by
  obtain ⟨κ, hκ, CD, hCD, happD⟩ := appD_epoch_hstar N r hr
  have hθm : 0 < thmin N r := thmin_pos N r
  set θm := thmin N r with hθmdef
  set C := CD / θm + κ + 1 with hCdef
  have hC : 0 ≤ C := by positivity
  obtain ⟨C', hC', h41⟩ := lemma_4_1 N r hr C hC
  refine ⟨κ, hκ, C' + 1, by linarith, ?_⟩
  intro lam hlam z s hGP sel hsel
  obtain ⟨hε, hε1⟩ := gap_facts N r lam hlam z s hGP
  have happD' := happD lam hlam z s hGP sel hsel
  set ε := gpGap z s with hεdef
  set τ := ⌈κ / ε⌉₊ with hτdef
  have hτ1 : 1 ≤ τ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr (div_pos hκ hε)).ne'
  have hτle : (τ : ℝ) ≤ (κ + 1) / ε := by
    have h1 := Nat.ceil_lt_add_one (div_pos hκ hε).le
    have h2 : 1 ≤ 1 / ε := by rw [le_div_iff₀ hε]; linarith
    rw [add_div]
    rw [← hτdef] at h1
    linarith
  have hfeas : ∀ u, StaticFeasible N u (sel u) := fun u => (hsel u).1
  have hadm := admissible N sel (Qplus s) τ hfeas
  refine ⟨hadm, ?_⟩
  obtain ⟨⟨θ, hθ, huniq⟩, hall⟩ := dual_theta N r hr lam hlam z s hGP
  obtain ⟨-, hθ0, -, -, hθpos⟩ := hall θ hθ
  have hθge : ∀ i ∈ Qzero s, θm ≤ θ i := fun i hi =>
    theta_ge N r z s θ hθ huniq hθpos i hi
  have hM0 : ∀ t ω, ∀ m ∈ Mzero z, resolvingPolicy N sel (Qplus s) τ t ω m = 0 := by
    intro t ω m hm
    unfold resolvingPolicy
    apply Finset.sum_eq_zero
    intro k _
    exact (hsel _).2.1 m hm
  have hQ : ∀ t : ℕ, 1 ≤ t → ∀ i ∈ Qzero s,
      expect lam t (fun ω => (queue N (resolvingPolicy N sel (Qplus s) τ) ω t i : ℝ)) ≤ C / ε := by
    intro t ht i hi
    have hiQ : i ∉ Qplus s := by simpa [Qzero, Qplus] using hi
    set k := (t - 1) / τ with hk
    set P : (ℕ → Fin n) → ℝ := fun ω =>
      (postMatch N sel (Qplus s) (epochQueue N sel (Qplus s) τ k ω) i : ℝ) with hP
    have h1 : expect lam t (fun ω => (queue N (resolvingPolicy N sel (Qplus s) τ) ω t i : ℝ)) ≤
        expect lam t (fun ω => P ω + (τ : ℝ)) := by
      apply expect_mono lam hlam
      intro ω
      have := queue_le N sel (Qplus s) τ hfeas hτ1 ω t ht i hiQ
      simp only [hP]
      exact_mod_cast this
    rw [expect_add, expect_const lam hlam] at h1
    have hPdep : ∀ ω ω', (∀ s' < k * τ, ω s' = ω' s') → P ω = P ω' := by
      intro ω ω' h
      simp only [hP]
      rw [epochQueue_congr N sel (Qplus s) τ k ω ω' h]
    have hkt : k * τ ≤ t := (Nat.div_mul_le_self (t - 1) τ).trans (by omega)
    rw [expect_ge lam hlam (k * τ) P hPdep t hkt] at h1
    have hPb : expect lam (k * τ) P ≤ CD / ε / θm := by
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · have : P = fun _ => 0 := by
          funext ω; simp [hP, hk0, epochQueue, postMatch]
        rw [this, expect_const lam hlam]
        positivity
      · have hA := happD' θ hθ k hkpos
        have hpw : ∀ ω, P ω ≤ (1 / θm) *
            hstar N z s θ (epochQueue N sel (Qplus s) τ k ω) := by
          intro ω
          have h2 := post_le_hstar N r z s θ hθ hθ0 sel hsel
            (epochQueue N sel (Qplus s) τ k ω) i hi
          have hθi := hθge i hi
          have hP0 : 0 ≤ P ω := Nat.cast_nonneg _
          have h3 : θm * P ω ≤ hstar N z s θ (epochQueue N sel (Qplus s) τ k ω) :=
            (mul_le_mul_of_nonneg_right hθi hP0).trans h2
          rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hθm]
          linarith
        have h4 := expect_mono lam hlam (k * τ) _ _ hpw
        rw [expect_const_mul] at h4
        calc expect lam (k * τ) P ≤ _ := h4
          _ ≤ (1 / θm) * (CD / ε) :=
            mul_le_mul_of_nonneg_left hA (by positivity)
          _ = CD / ε / θm := by ring
    have hfin : CD / ε / θm + (κ + 1) / ε = C / ε := by
      rw [hCdef]; field_simp; ring
    linarith
  have h41' := h41 lam hlam z s hGP _ hadm hM0 hQ
  intro t ht
  calc Rstar N lam r t - valueOf lam r (resolvingPolicy N sel (Qplus s) τ) t ≤ C' / ε :=
        h41' t ht
    _ ≤ (C' + 1) / ε := div_le_div_of_nonneg_right (by linarith) hε.le
