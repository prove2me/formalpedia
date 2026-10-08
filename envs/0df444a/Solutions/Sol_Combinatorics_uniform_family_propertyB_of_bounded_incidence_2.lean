-- Prove2me | solution 2 for Combinatorics.uniform_family_propertyB_of_bounded_incidence
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T08:11:12.919299+00:00
-- url     : https://prove2.me/submissions/f26495e1-0966-4499-9dfd-325e7398360f

import Mathlib

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace PBf0

variable {X I : Type*} [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]

def mono (B : I → Finset X) (i : I) (c : X → Bool) : Prop :=
  ∀ x ∈ B i, ∀ y ∈ B i, c x = c y

def good (B : I → Finset X) (S : Finset I) (c : X → Bool) : Prop :=
  ∀ j ∈ S, ¬ mono B j c

open Classical in
noncomputable def N (B : I → Finset X) (S : Finset I) : ℕ :=
  (Finset.univ.filter (fun c : X → Bool => good B S c)).card

open Classical in
noncomputable def Bd (B : I → Finset X) (i : I) (S : Finset I) : ℕ :=
  (Finset.univ.filter (fun c : X → Bool => mono B i c ∧ good B S c)).card

lemma mono_congr (B : I → Finset X) (j : I) (c c' : X → Bool)
    (h : ∀ x ∈ B j, c x = c' x) : mono B j c ↔ mono B j c' := by
  unfold mono
  constructor
  · intro H x hx y hy
    rw [← h x hx, ← h y hy]; exact H x hx y hy
  · intro H x hx y hy
    rw [h x hx, h y hy]; exact H x hx y hy

lemma N_insert (B : I → Finset X) (i : I) (S : Finset I) :
    N B (insert i S) + Bd B i S = N B S := by
  classical
  unfold N Bd
  rw [← Finset.card_filter_add_card_filter_not (p := fun c => mono B i c)
    (s := Finset.univ.filter (fun c : X → Bool => good B S c))]
  rw [Finset.filter_filter, Finset.filter_filter, add_comm]
  congr 2
  · ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  · ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    unfold good
    rw [Finset.forall_mem_insert]
    tauto

lemma N_empty (B : I → Finset X) : N B ∅ = 2 ^ Fintype.card X := by
  classical
  unfold N
  simp [good, Fintype.card_bool]

lemma Bd_mono (B : I → Finset X) (i : I) (S T : Finset I) (h : T ⊆ S) :
    Bd B i S ≤ Bd B i T := by
  classical
  unfold Bd
  apply Finset.card_le_card
  intro c hc
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
  unfold good at hc ⊢
  exact ⟨hc.1, fun j hj => hc.2 j (h hj)⟩

lemma indep (B : I → Finset X) (i : I) (S : Finset I) (hne : (B i).Nonempty)
    (hS : ∀ j ∈ S, Disjoint (B j) (B i)) :
    Bd B i S * 2 ^ (B i).card ≤ 2 * N B S := by
  classical
  let e := (Equiv.piEquivPiSubtypeProd (fun x => x ∈ B i) (fun _ => Bool)).symm
  have he : ∀ q x, e q x = if hx : x ∈ B i then q.1 ⟨x, hx⟩ else q.2 ⟨x, hx⟩ := by
    intro q x; rfl
  let Q : ({x // x ∉ B i} → Bool) → Prop := fun h => good B S (e (fun _ => false, h))
  let P1 : ({x // x ∈ B i} → Bool) → Prop := fun g => ∀ a b, g a = g b
  have hgood : ∀ q, good B S (e q) ↔ Q q.2 := by
    intro q
    simp only [Q, good]
    apply forall_congr'; intro j; apply imp_congr_right; intro hj
    apply not_congr
    apply mono_congr
    intro x hx
    have hxi : x ∉ B i := Finset.disjoint_left.mp (hS j hj) hx
    rw [he, he]; simp [hxi]
  have hmono : ∀ q, mono B i (e q) ↔ P1 q.1 := by
    intro q
    simp only [mono, P1, he]
    constructor
    · intro H a b
      have := H a.1 a.2 b.1 b.2
      simpa [a.2, b.2] using this
    · intro H x hx y hy
      simpa [hx, hy] using H ⟨x, hx⟩ ⟨y, hy⟩
  have hBd : Bd B i S = Fintype.card {g // P1 g} * Fintype.card {h // Q h} := by
    unfold Bd
    rw [← Fintype.card_subtype, ← Fintype.card_prod]
    symm
    refine Fintype.card_congr ((Equiv.subtypeProdEquivProd).symm.trans ?_)
    refine e.subtypeEquiv ?_
    intro q
    rw [hmono, hgood]
  have hN : N B S = 2 ^ (B i).card * Fintype.card {h // Q h} := by
    unfold N
    rw [← Fintype.card_subtype]
    have : Fintype.card ({x // x ∈ B i} → Bool) = 2 ^ (B i).card := by
      simp [Fintype.card_bool]
    rw [← this, ← Fintype.card_prod]
    symm
    refine Fintype.card_congr ((Equiv.prodCongr (Equiv.refl _) (Equiv.refl _)).trans ?_)
    refine (Equiv.subtypeUnivEquiv (p := fun _ => True) (fun _ => trivial)).symm.prodCongr
      (Equiv.refl _) |>.trans ?_
    refine (Equiv.subtypeProdEquivProd).symm.trans ?_
    refine e.subtypeEquiv ?_
    intro q
    rw [hgood]; simp
  have hP1 : Fintype.card {g // P1 g} ≤ 2 := by
    obtain ⟨x0, hx0⟩ := hne
    have : Fintype.card {g // P1 g} ≤ Fintype.card Bool := by
      apply Fintype.card_le_of_injective (fun g => g.1 ⟨x0, hx0⟩)
      intro g g' hgg
      apply Subtype.ext
      funext a
      rw [g.2 a ⟨x0, hx0⟩, g'.2 a ⟨x0, hx0⟩]
      exact hgg
    simpa using this
  rw [hBd, hN]
  calc Fintype.card {g // P1 g} * Fintype.card {h // Q h} * 2 ^ (B i).card
      ≤ 2 * Fintype.card {h // Q h} * 2 ^ (B i).card := by gcongr
    _ = 2 * (2 ^ (B i).card * Fintype.card {h // Q h}) := by ring

lemma chain (B : I → Finset X) (q : ℝ) (hq : 0 ≤ q) (n : ℕ)
    (H : ∀ U : Finset I, U.card < n → ∀ j ∉ U, q * (N B U : ℝ) ≤ N B (insert j U))
    (T : Finset I) : ∀ R : Finset I, Disjoint T R → T.card + R.card ≤ n →
      q ^ R.card * (N B T : ℝ) ≤ N B (T ∪ R) := by
  intro R
  induction R using Finset.induction_on with
  | empty => intro _ _; simp
  | insert a R ha ih =>
    intro hd hc
    rw [Finset.disjoint_insert_right] at hd
    rw [Finset.card_insert_of_notMem ha] at hc ⊢
    have h1 := ih hd.2 (by omega)
    have h2 := H (T ∪ R) (by
      calc (T ∪ R).card ≤ T.card + R.card := Finset.card_union_le _ _
        _ < n := by omega) a (by
      rw [Finset.mem_union]; exact fun h => h.elim hd.1 ha)
    rw [Finset.union_insert]
    calc q ^ (R.card + 1) * (N B T : ℝ) = q * (q ^ R.card * N B T) := by ring
      _ ≤ q * N B (T ∪ R) := mul_le_mul_of_nonneg_left h1 hq
      _ ≤ _ := h2

lemma claim (B : I → Finset X) (m K : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp : 2 ≤ p * 2 ^ m)
    (hsize : ∀ i, (B i).card = m) (hm : 0 < m)
    (hdeg : ∀ i, (Finset.univ.filter (fun j => ¬ Disjoint (B j) (B i))).card ≤ K)
    (hb : 4 * p * K ≤ 1) :
    ∀ n, ∀ S : Finset I, S.card = n → ∀ i ∉ S, (Bd B i S : ℝ) ≤ 2 * p * N B S := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hS i hi
  classical
  have hne : (B i).Nonempty := by
    rw [← Finset.card_pos, hsize]; exact hm
  set S2 := S.filter (fun j => Disjoint (B j) (B i)) with hS2
  set S1 := S.filter (fun j => ¬ Disjoint (B j) (B i)) with hS1
  have H : ∀ U : Finset I, U.card < S.card → ∀ j ∉ U,
      (1 - 2 * p) * (N B U : ℝ) ≤ N B (insert j U) := by
    intro U hU j hj
    have h1 := ih U.card (by omega) U rfl j hj
    have h2 := N_insert B j U
    have h3 : (N B (insert j U) : ℝ) + Bd B j U = N B U := by exact_mod_cast h2
    linarith
  have hq : 0 ≤ 1 - 2 * p := by
    have hK : 1 ≤ K := by
      refine le_trans ?_ (hdeg i)
      rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
      refine fun h => h i ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_self_iff_empty]
      exact hne.ne_empty
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    nlinarith
  have hcard : S2.card + S1.card = S.card := Finset.card_filter_add_card_filter_not _
  have hunion : S2 ∪ S1 = S := Finset.filter_union_filter_not_eq _ _
  have hdisj : Disjoint S2 S1 := Finset.disjoint_filter_filter_not _ _ _
  have hch := chain B (1 - 2 * p) hq S.card H S2 S1 hdisj (by omega)
  rw [hunion] at hch
  have hS1K : S1.card ≤ K := by
    refine le_trans (Finset.card_le_card ?_) (hdeg i)
    intro j hj
    simp only [hS1, Finset.mem_filter] at hj
    simp [hj.2]
  have hbern : 1 + (S1.card : ℝ) * (-(2 * p)) ≤ (1 - 2 * p) ^ S1.card := by
    have := one_add_mul_le_pow (a := -(2 * p)) (by linarith) S1.card
    simpa [sub_eq_add_neg] using this
  have hS1K' : (S1.card : ℝ) ≤ K := by exact_mod_cast hS1K
  have hhalf : (1 : ℝ) / 2 ≤ (1 - 2 * p) ^ S1.card := by nlinarith
  have hN2 : (0 : ℝ) ≤ N B S2 := by positivity
  have hNS2 : (N B S2 : ℝ) ≤ 2 * N B S := by
    have := mul_le_mul_of_nonneg_right hhalf hN2
    linarith
  have hind := indep B i S2 hne (by
    intro j hj
    simp only [hS2, Finset.mem_filter] at hj
    exact hj.2)
  rw [hsize] at hind
  have hind' : (Bd B i S2 : ℝ) * 2 ^ m ≤ 2 * N B S2 := by exact_mod_cast hind
  have hBd2 : (Bd B i S2 : ℝ) ≤ p * N B S2 := by
    have h2m : (0 : ℝ) < 2 ^ m := by positivity
    have : (Bd B i S2 : ℝ) * 2 ^ m ≤ (p * N B S2) * 2 ^ m := by
      have := mul_le_mul_of_nonneg_right hp hN2
      nlinarith
    exact le_of_mul_le_mul_right this h2m
  have hmono := Bd_mono B i S S2 (Finset.filter_subset _ _)
  have hmono' : (Bd B i S : ℝ) ≤ Bd B i S2 := by exact_mod_cast hmono
  calc (Bd B i S : ℝ) ≤ p * N B S2 := le_trans hmono' hBd2
    _ ≤ p * (2 * N B S) := mul_le_mul_of_nonneg_left hNS2 hp0
    _ = 2 * p * N B S := by ring

end PBf0

theorem solution
    (X I : Type*) [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]
    (B : I → Finset X) (m D : ℕ)
    (hm : 0 < m)
    (hsize : ∀ i, (B i).card = m)
    (hdegree : ∀ x, (Finset.univ.filter (fun i => x ∈ B i)).card ≤ D)
    (hcond : (4 : ℝ) * (m : ℝ) * (D : ℝ) * (2 : ℝ) ^ (1 - (m : ℝ)) < 1) :
    ∃ c : X → Bool, ∀ i,
      (∃ x ∈ B i, c x = true) ∧ (∃ x ∈ B i, c x = false) := by
  classical
  rcases isEmpty_or_nonempty I with hI | ⟨⟨i0⟩⟩
  · exact ⟨fun _ => true, fun i => isEmptyElim i⟩
  set p : ℝ := (2 : ℝ) ^ (1 - (m : ℝ)) with hpdef
  have hp2 : p * 2 ^ m = 2 := by
    rw [hpdef, Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_one, Real.rpow_natCast]
    field_simp
  have hp0 : 0 ≤ p := by positivity
  have hdeg : ∀ i, (Finset.univ.filter (fun j => ¬ Disjoint (B j) (B i))).card ≤ m * D := by
    intro i
    calc (Finset.univ.filter (fun j => ¬ Disjoint (B j) (B i))).card
        ≤ ((B i).biUnion (fun x => Finset.univ.filter (fun j => x ∈ B j))).card := by
          apply Finset.card_le_card
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            Finset.not_disjoint_iff] at hj
          obtain ⟨x, hx1, hx2⟩ := hj
          simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨x, hx2, hx1⟩
      _ ≤ ∑ x ∈ B i, (Finset.univ.filter (fun j => x ∈ B j)).card := Finset.card_biUnion_le
      _ ≤ ∑ _x ∈ B i, D := Finset.sum_le_sum (fun x _ => hdegree x)
      _ = m * D := by rw [Finset.sum_const, hsize, smul_eq_mul]
  have hb : 4 * p * ((m * D : ℕ) : ℝ) ≤ 1 := by
    push_cast
    nlinarith
  have hK : 1 ≤ m * D := by
    have hne : (B i0).Nonempty := by rw [← Finset.card_pos, hsize]; exact hm
    refine le_trans ?_ (hdeg i0)
    rw [Nat.one_le_iff_ne_zero, Ne, Finset.card_eq_zero, Finset.eq_empty_iff_forall_notMem]
    refine fun h => h i0 ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_self_iff_empty]
    exact hne.ne_empty
  have hK' : (1 : ℝ) ≤ ((m * D : ℕ) : ℝ) := by exact_mod_cast hK
  have hq : 0 < 1 - 2 * p := by nlinarith
  have hcl := PBf0.claim B m (m * D) p hp0 hp2.ge hsize hm hdeg hb
  have H : ∀ U : Finset I, U.card < Fintype.card I → ∀ j ∉ U,
      (1 - 2 * p) * (PBf0.N B U : ℝ) ≤ PBf0.N B (insert j U) := by
    intro U _ j hj
    have h1 := hcl U.card U rfl j hj
    have h3 : (PBf0.N B (insert j U) : ℝ) + PBf0.Bd B j U = PBf0.N B U := by
      exact_mod_cast PBf0.N_insert B j U
    linarith
  have hch := PBf0.chain B (1 - 2 * p) hq.le (Fintype.card I) H ∅ Finset.univ
    (Finset.disjoint_empty_left _) (by simp)
  rw [Finset.empty_union, PBf0.N_empty] at hch
  have hpos : (0 : ℝ) < PBf0.N B Finset.univ := by
    refine lt_of_lt_of_le ?_ hch
    positivity
  have hpos' : 0 < PBf0.N B Finset.univ := by exact_mod_cast hpos
  unfold PBf0.N at hpos'
  obtain ⟨c, hc⟩ := Finset.card_pos.mp hpos'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc
  refine ⟨c, fun i => ?_⟩
  have hci := hc i (Finset.mem_univ i)
  unfold PBf0.mono at hci
  simp only [not_forall] at hci
  obtain ⟨x, hx, y, hy, hxy⟩ := hci
  cases hcx : c x with
  | true =>
    refine ⟨⟨x, hx, hcx⟩, ⟨y, hy, ?_⟩⟩
    rw [hcx] at hxy
    cases hcy : c y <;> simp_all
  | false =>
    refine ⟨⟨y, hy, ?_⟩, ⟨x, hx, hcx⟩⟩
    rw [hcx] at hxy
    cases hcy : c y <;> simp_all
