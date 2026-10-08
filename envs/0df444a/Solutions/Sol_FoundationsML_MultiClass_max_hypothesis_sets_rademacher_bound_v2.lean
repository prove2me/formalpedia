-- Prove2me | solution 1 for FoundationsML.MultiClass.max_hypothesis_sets_rademacher_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:28:56.660986+00:00
-- url     : https://prove2.me/submissions/186046e6-478b-429f-95d8-8182dbd59a28

import Mathlib
import Definitions.Def_FoundationsML_MultiClass_EmpiricalRademacherComplexity_v2
import Definitions.Def_FoundationsML_MultiClass_MaxFamily



namespace FoundationsML.MultiClass

noncomputable def aux_mr_sg (b : Bool) : ℝ := if b then 1 else -1

noncomputable def aux_mr_L {m : ℕ} (σ : Fin m → Bool) (v : Fin m → ℝ) : ℝ :=
  ∑ i, aux_mr_sg (σ i) * v i

noncomputable def aux_mr_R {m : ℕ} {P : Type*} (e : P → Fin m → ℝ) : ℝ :=
  ∑ σ : Fin m → Bool, ⨆ p, aux_mr_L σ (e p)

lemma aux_mr_sg_le (b : Bool) (x : ℝ) : aux_mr_sg b * x ≤ |x| := by
  cases b <;> simp [aux_mr_sg, le_abs_self, neg_le_abs]

lemma aux_mr_bdd {m : ℕ} {P : Type*} (e : P → Fin m → ℝ) (M : ℝ)
    (hb : ∀ p i, |e p i| ≤ M) (σ : Fin m → Bool) :
    BddAbove (Set.range fun p => aux_mr_L σ (e p)) := by
  refine ⟨∑ _i : Fin m, M, ?_⟩
  rintro _ ⟨p, rfl⟩
  exact Finset.sum_le_sum fun i _ => (aux_mr_sg_le _ _).trans (hb p i)

lemma aux_mr_key2 {P : Type*} [Nonempty P] (x u : P → ℝ) (C : ℝ)
    (hC : ∀ p, |x p| ≤ C ∧ |u p| ≤ C) :
    (⨆ p, (|x p| + u p)) + (⨆ p, (-|x p| + u p)) ≤
      (⨆ p, (x p + u p)) + (⨆ p, (-x p + u p)) := by
  have hA : BddAbove (Set.range fun p => x p + u p) := by
    refine ⟨C + C, ?_⟩
    rintro _ ⟨p, rfl⟩
    have := hC p; have h1 := le_abs_self (x p); have h2 := le_abs_self (u p); linarith
  have hB : BddAbove (Set.range fun p => -x p + u p) := by
    refine ⟨C + C, ?_⟩
    rintro _ ⟨p, rfl⟩
    have := hC p; have h1 := neg_le_abs (x p); have h2 := le_abs_self (u p); linarith
  set RHS := (⨆ p, (x p + u p)) + (⨆ p, (-x p + u p)) with hRHS
  have main : ∀ p q, (|x p| + u p) + (-|x q| + u q) ≤ RHS := by
    intro p q
    have a1 := le_ciSup hA p; have a2 := le_ciSup hA q
    have b1 := le_ciSup hB p; have b2 := le_ciSup hB q
    have habs : |x p| - |x q| ≤ |x p - x q| := abs_sub_abs_le_abs_sub _ _
    rcases le_total (x q) (x p) with h | h
    · rw [abs_of_nonneg (by linarith : 0 ≤ x p - x q)] at habs

      linarith
    · rw [abs_of_nonpos (by linarith : x p - x q ≤ 0)] at habs

      linarith
  have h1 : ∀ p, |x p| + u p ≤ RHS - ⨆ q, (-|x q| + u q) := by
    intro p
    have : (⨆ q, (-|x q| + u q)) ≤ RHS - (|x p| + u p) :=
      ciSup_le fun q => by linarith [main p q]
    linarith
  have := ciSup_le h1
  linarith

lemma aux_mr_split {m : ℕ} (σ : Fin m → Bool) (v : Fin m → ℝ) (j : Fin m) :
    aux_mr_L σ v = aux_mr_sg (σ j) * v j +
      ∑ i ∈ Finset.univ.erase j, aux_mr_sg (σ i) * v i := by
  unfold aux_mr_L
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]

lemma aux_mr_flip_sum {m : ℕ} (j : Fin m) (f : (Fin m → Bool) → ℝ) :
    ∑ σ, f σ = ∑ σ, f (Function.update σ j (!σ j)) := by
  have hinv : Function.Involutive (fun σ : Fin m → Bool => Function.update σ j (!σ j)) := by
    intro σ
    simp
  exact (Equiv.sum_comp hinv.toPerm f).symm

lemma aux_mr_contr1 {m : ℕ} {P : Type*} [Nonempty P] (e : P → Fin m → ℝ) (M : ℝ)
    (hb : ∀ p i, |e p i| ≤ M) (j : Fin m) :
    aux_mr_R (fun p => Function.update (e p) j |e p j|) ≤ aux_mr_R e := by
  unfold aux_mr_R
  set e' := fun p => Function.update (e p) j |e p j| with he'
  have hpt : ∀ σ : Fin m → Bool,
      (⨆ p, aux_mr_L σ (e' p)) + (⨆ p, aux_mr_L (Function.update σ j (!σ j)) (e' p)) ≤
      (⨆ p, aux_mr_L σ (e p)) + (⨆ p, aux_mr_L (Function.update σ j (!σ j)) (e p)) := by
    intro σ
    set σ' := Function.update σ j (!σ j)
    set u : P → ℝ := fun p => ∑ i ∈ Finset.univ.erase j, aux_mr_sg (σ i) * e p i with hu
    have hU1 : ∀ p, ∑ i ∈ Finset.univ.erase j, aux_mr_sg (σ i) * e' p i = u p := by
      intro p
      refine Finset.sum_congr rfl fun i hi => ?_
      have : i ≠ j := Finset.ne_of_mem_erase hi
      simp [he', Function.update_of_ne this]
    have hU2 : ∀ (v : Fin m → ℝ), ∑ i ∈ Finset.univ.erase j, aux_mr_sg (σ' i) * v i =
        ∑ i ∈ Finset.univ.erase j, aux_mr_sg (σ i) * v i := by
      intro v
      refine Finset.sum_congr rfl fun i hi => ?_
      have : i ≠ j := Finset.ne_of_mem_erase hi
      simp [σ', Function.update_of_ne this]
    have hσ'j : σ' j = !σ j := by simp [σ']
    have hC : ∀ p, |e p j| ≤ ((Finset.univ : Finset (Fin m)).card * M + M) ∧
        |u p| ≤ ((Finset.univ : Finset (Fin m)).card * M + M) := by
      intro p
      have hM : 0 ≤ M := (abs_nonneg _).trans (hb p j)
      refine ⟨by nlinarith [hb p j, (Finset.univ : Finset (Fin m)).card.cast_nonneg (α := ℝ)], ?_⟩
      have : |u p| ≤ ∑ i ∈ Finset.univ.erase j, |aux_mr_sg (σ i) * e p i| :=
        Finset.abs_sum_le_sum_abs _ _
      have h2 : ∑ i ∈ Finset.univ.erase j, |aux_mr_sg (σ i) * e p i| ≤
          ∑ i ∈ Finset.univ.erase j, M := by
        refine Finset.sum_le_sum fun i _ => ?_
        have : |aux_mr_sg (σ i)| = 1 := by cases σ i <;> simp [aux_mr_sg]
        rw [abs_mul, this, one_mul]; exact hb p i
      have h3 : ∑ i ∈ Finset.univ.erase j, M ≤ ∑ i : Fin m, M :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun _ _ _ => hM
      simp only [Finset.sum_const, nsmul_eq_mul] at h2 h3
      linarith
    have e1 : ∀ p, aux_mr_L σ (e' p) = aux_mr_sg (σ j) * |e p j| + u p := by
      intro p; rw [aux_mr_split σ _ j, hU1]; simp [he']
    have e2 : ∀ p, aux_mr_L σ' (e' p) = -(aux_mr_sg (σ j) * |e p j|) + u p := by
      intro p; rw [aux_mr_split σ' _ j, hU2, hU1, hσ'j]
      cases σ j <;> simp [he', aux_mr_sg]
    have e3 : ∀ p, aux_mr_L σ (e p) = aux_mr_sg (σ j) * e p j + u p := by
      intro p; rw [aux_mr_split σ _ j]
    have e4 : ∀ p, aux_mr_L σ' (e p) = -(aux_mr_sg (σ j) * e p j) + u p := by
      intro p; rw [aux_mr_split σ' (e p) j, hU2, hσ'j]
      congr 1
      cases σ j <;> simp [aux_mr_sg]
    simp only [e1, e2, e3, e4]
    cases σ j
    · simp only [aux_mr_sg, Bool.false_eq_true, ↓reduceIte, neg_mul, one_mul, neg_neg]
      have := aux_mr_key2 (fun p => e p j) u _ hC
      linarith
    · simp only [aux_mr_sg, ↓reduceIte, one_mul]
      exact aux_mr_key2 (fun p => e p j) u _ hC
  have h1 := aux_mr_flip_sum j (fun σ => ⨆ p, aux_mr_L σ (e' p))
  have h2 := aux_mr_flip_sum j (fun σ => ⨆ p, aux_mr_L σ (e p))
  have h3 := Finset.sum_le_sum (s := Finset.univ) fun σ _ => hpt σ
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at h3
  simp only at h1 h2
  linarith

lemma aux_mr_contr {m : ℕ} {P : Type*} [Nonempty P] (e : P → Fin m → ℝ) (M : ℝ)
    (hb : ∀ p i, |e p i| ≤ M) :
    aux_mr_R (fun p i => |e p i|) ≤ aux_mr_R e := by
  have key : ∀ T : Finset (Fin m),
      aux_mr_R (fun p i => if i ∈ T then |e p i| else e p i) ≤ aux_mr_R e := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert j T hj ih =>
      have heq : (fun p i => if i ∈ insert j T then |e p i| else e p i) =
          fun p => Function.update (fun i => if i ∈ T then |e p i| else e p i) j
            |(fun i => if i ∈ T then |e p i| else e p i) j| := by
        funext p i
        by_cases hij : i = j
        · subst hij; simp [hj]
        · simp [Function.update_of_ne hij, hij]
      rw [heq]
      refine le_trans (aux_mr_contr1 _ M ?_ j) ih
      intro p i
      split_ifs
      · rw [abs_abs]; exact hb p i
      · exact hb p i
  simpa using key Finset.univ

lemma aux_mr_add {m : ℕ} {P : Type*} [Nonempty P] (a b : P → Fin m → ℝ) (M : ℝ)
    (ha : ∀ p i, |a p i| ≤ M) (hb : ∀ p i, |b p i| ≤ M) :
    aux_mr_R (fun p => a p + b p) ≤ aux_mr_R a + aux_mr_R b := by
  unfold aux_mr_R
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun σ _ => ?_
  refine ciSup_le fun p => ?_
  have hL : aux_mr_L σ (a p + b p) = aux_mr_L σ (a p) + aux_mr_L σ (b p) := by
    simp [aux_mr_L, mul_add, Finset.sum_add_distrib]
  rw [hL]
  exact add_le_add (le_ciSup (aux_mr_bdd a M ha σ) p) (le_ciSup (aux_mr_bdd b M hb σ) p)

lemma aux_mr_smul {m : ℕ} {P : Type*} (e : P → Fin m → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    aux_mr_R (fun p => c • e p) = c * aux_mr_R e := by
  unfold aux_mr_R
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Real.mul_iSup_of_nonneg hc]
  congr 1; funext p
  simp [aux_mr_L, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => by ring

lemma aux_mr_neg {m : ℕ} {P : Type*} (e : P → Fin m → ℝ) :
    aux_mr_R (fun p => -e p) = aux_mr_R e := by
  unfold aux_mr_R
  have hinv : Function.Involutive (fun σ : Fin m → Bool => fun i => !σ i) := by
    intro σ; funext i; simp
  rw [← Equiv.sum_comp hinv.toPerm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1; funext p
  simp only [aux_mr_L, Function.Involutive.coe_toPerm]
  refine Finset.sum_congr rfl fun i _ => ?_
  cases σ i <;> simp [aux_mr_sg]

lemma aux_mr_max {m : ℕ} {P : Type*} [Nonempty P] (a b : P → Fin m → ℝ) (M : ℝ)
    (ha : ∀ p i, |a p i| ≤ M) (hb : ∀ p i, |b p i| ≤ M) :
    aux_mr_R (fun p i => max (a p i) (b p i)) ≤ aux_mr_R a + aux_mr_R b := by
  have heq : (fun p i => max (a p i) (b p i)) =
      fun p => (1 / 2 : ℝ) • (a p + b p) + (1 / 2 : ℝ) • (fun i => |(a p + -b p) i|) := by
    funext p i
    simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul]
    rcases le_total (a p i) (b p i) with h | h
    · rw [max_eq_right h, abs_of_nonpos (by linarith)]; ring
    · rw [max_eq_left h, abs_of_nonneg (by linarith)]; ring
  rw [heq]
  have hab : ∀ p i, |(a p + b p) i| ≤ M + M := fun p i => by
    simp only [Pi.add_apply]; exact (abs_add_le _ _).trans (add_le_add (ha p i) (hb p i))
  have hanb : ∀ p i, |(a p + -b p) i| ≤ M + M := fun p i => by
    simp only [Pi.add_apply, Pi.neg_apply]
    exact (abs_add_le _ _).trans (add_le_add (ha p i) (by rw [abs_neg]; exact hb p i))
  have hs1 : ∀ p i, |((1 / 2 : ℝ) • (a p + b p)) i| ≤ (1 / 2) * (M + M) := fun p i => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left (hab p i) (by norm_num)
  have hs2 : ∀ p i, |((1 / 2 : ℝ) • (fun i => |(a p + -b p) i|)) i| ≤ (1 / 2) * (M + M) :=
    fun p i => by
    simp only [Pi.smul_apply, smul_eq_mul, abs_mul, abs_abs]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
    exact mul_le_mul_of_nonneg_left (hanb p i) (by norm_num)
  refine (aux_mr_add _ _ _ hs1 hs2).trans ?_
  rw [aux_mr_smul _ _ (by norm_num), aux_mr_smul (fun p i => |(a p + -b p) i|) _ (by norm_num)]
  have h1 := aux_mr_add a b M ha hb
  have h2 := aux_mr_contr (fun p => a p + -b p) (M + M) hanb
  have hnb : ∀ p i, |(-b p) i| ≤ M := fun p i => by simp only [Pi.neg_apply, abs_neg]; exact hb p i
  have h3 := aux_mr_add a (fun p => -b p) M ha hnb
  rw [aux_mr_neg] at h3
  linarith

lemma aux_mr_eval {m : ℕ} {ι : Type*} {P : ι → Type*} [∀ j, Nonempty (P j)]
    (e : ∀ j, P j → Fin m → ℝ) (a : ι) :
    aux_mr_R (fun h : (∀ j, P j) => e a (h a)) = aux_mr_R (e a) := by
  unfold aux_mr_R
  refine Finset.sum_congr rfl fun σ _ => ?_
  exact (Function.surjective_eval a).iSup_comp (fun p => aux_mr_L σ (e a p))

lemma aux_mr_finset {m : ℕ} {ι : Type*} [DecidableEq ι] {P : ι → Type*} [∀ j, Nonempty (P j)]
    (e : ∀ j, P j → Fin m → ℝ) (M : ℝ) (hb : ∀ j p i, |e j p i| ≤ M)
    (s : Finset ι) (hs : s.Nonempty) :
    aux_mr_R (fun (h : ∀ j, P j) i => s.sup' hs (fun j => e j (h j) i)) ≤
      ∑ j ∈ s, aux_mr_R (e j) := by
  induction hs using Finset.Nonempty.cons_induction with
  | singleton a =>
    simp only [Finset.sup'_singleton, Finset.sum_singleton]
    exact (aux_mr_eval e a).le
  | cons a s ha hs ih =>
    simp only [Finset.sup'_cons hs, Finset.sum_cons]
    have hbV : ∀ (h : ∀ j, P j) i, |s.sup' hs (fun j => e j (h j) i)| ≤ M := by
      intro h i
      rw [abs_le]
      obtain ⟨j0, hj0⟩ := hs
      constructor
      · exact le_trans (abs_le.mp (hb j0 (h j0) i)).1 (Finset.le_sup' (fun j => e j (h j) i) hj0)
      · exact Finset.sup'_le _ _ fun j _ => (abs_le.mp (hb j (h j) i)).2
    have := aux_mr_max (fun (h : ∀ j, P j) => e a (h a))
      (fun (h : ∀ j, P j) i => s.sup' hs (fun j => e j (h j) i)) M (fun h i => hb a (h a) i) hbV
    rw [aux_mr_eval] at this
    linarith

lemma aux_mr_erc_range {X Q : Type*} {m : ℕ} (φ : Q → X → ℝ) (S : Fin m → X) :
    EmpiricalRademacherComplexity (Set.range φ) S =
      (1 / (2 : ℝ) ^ m) * aux_mr_R (fun q i => (1 / (m : ℝ)) * φ q (S i)) := by
  unfold EmpiricalRademacherComplexity aux_mr_R
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← Set.range_comp]
  unfold iSup
  congr 1
  ext x
  simp only [Set.mem_range, Function.comp_apply, aux_mr_L, aux_mr_sg]
  constructor <;> rintro ⟨q, rfl⟩ <;> refine ⟨q, ?_⟩ <;>
    · rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => by ring

lemma aux_mr_R_nonneg {m : ℕ} {P : Type*} [Nonempty P] (e : P → Fin m → ℝ) (M : ℝ)
    (hb : ∀ p i, |e p i| ≤ M) : 0 ≤ aux_mr_R e := by
  have h1 := aux_mr_neg e
  have h2 : 0 ≤ aux_mr_R e + aux_mr_R (fun p => -e p) := by
    unfold aux_mr_R
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_nonneg fun σ _ => ?_
    obtain ⟨p⟩ := ‹Nonempty P›
    have hnb : ∀ p i, |(-e p) i| ≤ M := fun p i => by
      simp only [Pi.neg_apply, abs_neg]; exact hb p i
    have a1 := le_ciSup (aux_mr_bdd e M hb σ) p
    have a2 := le_ciSup (aux_mr_bdd (fun p => -e p) M hnb σ) p
    have : aux_mr_L σ (-e p) = -aux_mr_L σ (e p) := by
      simp [aux_mr_L, Finset.sum_neg_distrib]
    beta_reduce at a2
    linarith
  linarith

lemma aux_mr_erc_nonneg {X : Type*} {m : ℕ} (G : Set (X → ℝ)) (a b : ℝ)
    (hG : ∀ g ∈ G, ∀ x, g x ∈ Set.Icc a b) (S : Fin m → X) :
    0 ≤ EmpiricalRademacherComplexity G S := by
  rcases G.eq_empty_or_nonempty with h | h
  · subst h; simp [EmpiricalRademacherComplexity]
  · have hG' : G = Set.range (fun g : G => (g : X → ℝ)) := Subtype.range_coe.symm
    rw [hG', aux_mr_erc_range]
    haveI : Nonempty G := h.to_subtype
    refine mul_nonneg (by positivity) (aux_mr_R_nonneg _ ((1 / (m:ℝ)) * (|a| + |b|)) ?_)
    intro g i
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (m:ℝ))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := hG g.1 g.2 (S i)
    rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;>
      linarith [this.1, this.2]

theorem maxrad_core {X ι : Type*} [Fintype ι] [Nonempty ι] (F : ι → Set (X → ℝ))
    (hFb : ∃ a b : ℝ, ∀ j, ∀ g ∈ F j, ∀ x, g x ∈ Set.Icc a b)
    (m : ℕ) (S : Fin m → X) :
    EmpiricalRademacherComplexity (MaxFamily F) S ≤
      ∑ j, EmpiricalRademacherComplexity (F j) S := by
  classical
  obtain ⟨a, b, hab⟩ := hFb
  have hRHS : 0 ≤ ∑ j, EmpiricalRademacherComplexity (F j) S :=
    Finset.sum_nonneg fun j _ => aux_mr_erc_nonneg (F j) a b (hab j) S
  by_cases hE : ∃ j, F j = ∅
  · obtain ⟨j0, hj0⟩ := hE
    have : MaxFamily F = ∅ := by
      ext g
      simp only [MaxFamily, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h, hh, -⟩
      have := hh j0
      rw [hj0] at this
      exact this
    rw [this]
    simpa [EmpiricalRademacherComplexity] using hRHS
  push_neg at hE
  haveI : ∀ j, Nonempty (F j) := fun j => (hE j).to_subtype
  have hMF : MaxFamily F = Set.range (fun (h : ∀ j, F j) => fun x => ⨆ j, (h j).1 x) := by
    ext g
    simp only [MaxFamily, Set.mem_setOf_eq, Set.mem_range]
    constructor
    · rintro ⟨h, hh, rfl⟩; exact ⟨fun j => ⟨h j, hh j⟩, rfl⟩
    · rintro ⟨h, rfl⟩; exact ⟨fun j => (h j).1, fun j => (h j).2, rfl⟩
  have hFj : ∀ j, F j = Set.range (fun g : F j => (g : X → ℝ)) := fun j => Subtype.range_coe.symm
  rw [hMF, aux_mr_erc_range]
  conv_rhs => arg 2; ext j; rw [hFj j, aux_mr_erc_range]
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  set e : ∀ j, F j → Fin m → ℝ := fun j g i => (1 / (m : ℝ)) * g.1 (S i) with he
  have hb : ∀ j p i, |e j p i| ≤ (1 / (m:ℝ)) * (|a| + |b|) := by
    intro j g i
    simp only [he]
    rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / (m:ℝ))]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := hab j g.1 g.2 (S i)
    rw [abs_le]; constructor <;> cases abs_cases a <;> cases abs_cases b <;>
      linarith [this.1, this.2]
  have key := aux_mr_finset e _ hb Finset.univ Finset.univ_nonempty
  have heq : (fun (h : ∀ j, F j) i => (1 / (m : ℝ)) * (fun x => ⨆ j, (h j).1 x) (S i)) =
      (fun (h : ∀ j, F j) i => Finset.univ.sup' Finset.univ_nonempty (fun j => e j (h j) i)) := by
    funext h i
    rw [Finset.sup'_univ_eq_ciSup]
    simp only [he]
    rw [Real.mul_iSup_of_nonneg (by positivity)]
  rw [heq]
  exact key

end FoundationsML.MultiClass

open FoundationsML.MultiClass


theorem solution
    {X ι : Type*} [Fintype ι] [Nonempty ι] (F : ι → Set (X → ℝ))
    (hFb : ∃ a b : ℝ, ∀ j, ∀ g ∈ F j, ∀ x, g x ∈ Set.Icc a b)
    (m : ℕ) (S : Fin m → X) :
    EmpiricalRademacherComplexity (MaxFamily F) S ≤
      ∑ j, EmpiricalRademacherComplexity (F j) S := by
  exact maxrad_core F hFb m S
