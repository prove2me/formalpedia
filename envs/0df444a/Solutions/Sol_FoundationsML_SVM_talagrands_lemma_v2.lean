-- Prove2me | solution 1 for FoundationsML.SVM.talagrands_lemma_v2
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T17:31:06.958159+00:00
-- url     : https://prove2.me/submissions/ffd14a0e-1d86-4f5a-9b3d-d790dd846c07

import Mathlib
import Definitions.Def_FoundationsML_SVM_EmpiricalRademacherComplexity_v2



namespace FoundationsML.SVM

lemma tal_lipbd (φ : ℝ → ℝ) (L : ℝ) (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|) (a b t : ℝ)
    (ht : t ∈ Set.Icc a b) : |φ t| ≤ |φ a| + L * (b - a) := by
  have h1 := hφ t a
  have h2 : |t - a| ≤ b - a := by rw [abs_le]; constructor <;> linarith [ht.1, ht.2]
  have hL : 0 ≤ L := by
    by_contra hL; push_neg at hL
    have := hφ 1 0; norm_num at this; linarith [abs_nonneg (φ 1 - φ 0)]
  have h3 : |φ t| ≤ |φ t - φ a| + |φ a| := by
    calc |φ t| = |(φ t - φ a) + φ a| := by ring_nf
      _ ≤ _ := abs_add_le _ _
  nlinarith

lemma tal_key {α : Type*} (H : Set α) (u p : α → ℝ) (φ : ℝ → ℝ) (L : ℝ)
    (hφ : ∀ x y, |φ x - φ y| ≤ L * |x - y|) (e : ℝ) (he : e = 1 ∨ e = -1)
    (B a b : ℝ) (hu : ∀ h ∈ H, |u h| ≤ B) (hp : ∀ h ∈ H, p h ∈ Set.Icc a b) :
    sSup ((fun h => u h + e * φ (p h)) '' H) + sSup ((fun h => u h + (-e) * φ (p h)) '' H)
      ≤ sSup ((fun h => u h + e * (L * p h)) '' H)
        + sSup ((fun h => u h + (-e) * (L * p h)) '' H) := by
  rcases H.eq_empty_or_nonempty with hH | hH
  · subst hH; simp
  have hL : 0 ≤ L := by
    by_contra hL; push_neg at hL
    have := hφ 1 0; norm_num at this; linarith [abs_nonneg (φ 1 - φ 0)]
  have hb : ∀ h ∈ H, |φ (p h)| ≤ |φ a| + L * (b - a) := fun h hh => tal_lipbd φ L hφ a b _ (hp h hh)
  have hpb : ∀ h ∈ H, |p h| ≤ |a| + |b| := by
    intro h hh; have := hp h hh; rw [abs_le]
    constructor <;> cases abs_cases a <;> cases abs_cases b <;> linarith [this.1, this.2]
  have he' : |e| = 1 := by rcases he with rfl | rfl <;> norm_num
  have bdd : ∀ g : ℝ → ℝ, (∀ h ∈ H, |g (p h)| ≤ |φ a| + L * (b - a) + L * (|a| + |b|)) →
      ∀ e' : ℝ, |e'| = 1 → BddAbove ((fun h => u h + e' * g (p h)) '' H) := by
    intro g hg e' he''
    refine ⟨B + (|φ a| + L * (b - a) + L * (|a| + |b|)), ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    have h1 := hu h hh
    have h2 := hg h hh
    have : e' * g (p h) ≤ |e' * g (p h)| := le_abs_self _
    rw [abs_mul, he'', one_mul] at this
    have := (abs_le.mp h1).2
    simp only; linarith
  have hgφ : ∀ h ∈ H, |φ (p h)| ≤ |φ a| + L * (b - a) + L * (|a| + |b|) := by
    intro h hh; have := hb h hh; nlinarith [abs_nonneg a, abs_nonneg b]
  have hgL : ∀ h ∈ H, |L * p h| ≤ |φ a| + L * (b - a) + L * (|a| + |b|) := by
    intro h hh
    have h1 := hpb h hh
    have hab : a ≤ b := (hp h hh).1.trans (hp h hh).2
    rw [abs_mul, abs_of_nonneg hL]
    nlinarith [abs_nonneg (φ a)]
  have heN : |-e| = 1 := by rw [abs_neg, he']
  have b1 := bdd φ hgφ e he'
  have b2 := bdd φ hgφ (-e) heN
  have b3 := bdd (fun t => L * t) hgL e he'
  have b4 := bdd (fun t => L * t) hgL (-e) heN
  have ne : ∀ g : α → ℝ, (g '' H).Nonempty := fun g => hH.image g
  rw [← le_sub_iff_add_le]
  apply csSup_le (ne _)
  rintro _ ⟨h, hh, rfl⟩
  rw [le_sub_iff_add_le, ← le_sub_iff_add_le']
  apply csSup_le (ne _)
  rintro _ ⟨h', hh', rfl⟩
  rw [le_sub_iff_add_le']
  have hlip : e * φ (p h) + (-e) * φ (p h') ≤ L * |p h - p h'| := by
    have := hφ (p h) (p h')
    have : e * (φ (p h) - φ (p h')) ≤ |e * (φ (p h) - φ (p h'))| := le_abs_self _
    rw [abs_mul, he', one_mul] at this
    linarith
  rcases le_total (p h') (p h) with hle | hle
  · rw [abs_of_nonneg (by linarith)] at hlip
    rcases he with rfl | rfl
    · have c1 := le_csSup b3 ⟨h, hh, rfl⟩
      have c2 := le_csSup b4 ⟨h', hh', rfl⟩
      simp only at c1 c2 ⊢; nlinarith
    · have c1 := le_csSup b3 ⟨h', hh', rfl⟩
      have c2 := le_csSup b4 ⟨h, hh, rfl⟩
      simp only at c1 c2 ⊢; nlinarith
  · rw [abs_of_nonpos (by linarith)] at hlip
    rcases he with rfl | rfl
    · have c1 := le_csSup b3 ⟨h', hh', rfl⟩
      have c2 := le_csSup b4 ⟨h, hh, rfl⟩
      simp only at c1 c2 ⊢; nlinarith
    · have c1 := le_csSup b3 ⟨h, hh, rfl⟩
      have c2 := le_csSup b4 ⟨h', hh', rfl⟩
      simp only at c1 c2 ⊢; nlinarith

noncomputable def talSg (b : Bool) : ℝ := if b then 1 else -1

noncomputable def talG {X : Type*} {m : ℕ} (H : Set (X → ℝ)) (S : Fin m → X)
    (Ψ : Fin m → ℝ → ℝ) (σ : Fin m → Bool) : ℝ :=
  sSup ((fun h : X → ℝ => ∑ i : Fin m, talSg (σ i) * Ψ i (h (S i))) '' H)

lemma tal_step {X : Type*} {m : ℕ} (H : Set (X → ℝ)) (S : Fin m → X) (a b : ℝ)
    (hHb : ∀ h ∈ H, ∀ x, h x ∈ Set.Icc a b) (Ψ : Fin m → ℝ → ℝ) (L : ℝ)
    (hΨ : ∀ i x y, |Ψ i x - Ψ i y| ≤ L * |x - y|) (j : Fin m) :
    ∑ σ, talG H S Ψ σ ≤ ∑ σ, talG H S (Function.update Ψ j (fun t => L * t)) σ := by
  classical
  set fl : (Fin m → Bool) → (Fin m → Bool) := fun σ => Function.update σ j (!σ j) with hfl
  have finv : Function.Involutive fl := by
    intro σ; funext i
    by_cases hi : i = j
    · subst hi; simp [hfl]
    · simp [hfl, Function.update_of_ne hi]
  have hsum : ∀ G : (Fin m → Bool) → ℝ, ∑ σ, G (fl σ) = ∑ σ, G σ := fun G =>
    Equiv.sum_comp finv.toPerm G
  have hj : j ∈ (Finset.univ : Finset (Fin m)) := Finset.mem_univ j
  -- decomposition
  have dec : ∀ (σ : Fin m → Bool) (Ψ' : Fin m → ℝ → ℝ) (h : X → ℝ),
      ∑ i, talSg (σ i) * Ψ' i (h (S i)) =
        (∑ i ∈ Finset.univ.erase j, talSg (σ i) * Ψ' i (h (S i))) + talSg (σ j) * Ψ' j (h (S j)) :=
    fun σ Ψ' h => (Finset.sum_erase_add _ _ hj).symm
  have pt : ∀ σ, talG H S Ψ σ + talG H S Ψ (fl σ) ≤
      talG H S (Function.update Ψ j (fun t => L * t)) σ +
        talG H S (Function.update Ψ j (fun t => L * t)) (fl σ) := by
    intro σ
    set u : (X → ℝ) → ℝ := fun h => ∑ i ∈ Finset.univ.erase j, talSg (σ i) * Ψ i (h (S i))
      with hu
    have eu1 : ∀ h : X → ℝ, ∑ i ∈ Finset.univ.erase j, talSg (fl σ i) * Ψ i (h (S i)) = u h := by
      intro h; apply Finset.sum_congr rfl; intro i hi
      rw [Finset.mem_erase] at hi; simp [hfl, Function.update_of_ne hi.1]
    have eu2 : ∀ (σ' : Fin m → Bool) (h : X → ℝ),
        ∑ i ∈ Finset.univ.erase j, talSg (σ' i) * Function.update Ψ j (fun t => L * t) i (h (S i))
          = ∑ i ∈ Finset.univ.erase j, talSg (σ' i) * Ψ i (h (S i)) := by
      intro σ' h; apply Finset.sum_congr rfl; intro i hi
      rw [Finset.mem_erase] at hi; simp [Function.update_of_ne hi.1]
    have sfl : talSg (fl σ j) = - talSg (σ j) := by
      simp only [hfl, Function.update_self]; cases σ j <;> simp [talSg]
    have he : talSg (σ j) = 1 ∨ talSg (σ j) = -1 := by cases σ j <;> simp [talSg]
    have e1 : talG H S Ψ σ = sSup ((fun h => u h + talSg (σ j) * Ψ j (h (S j))) '' H) := by
      unfold talG; congr 2; funext h; rw [dec]
    have e2 : talG H S Ψ (fl σ) = sSup ((fun h => u h + (- talSg (σ j)) * Ψ j (h (S j))) '' H) := by
      unfold talG; congr 2; funext h; rw [dec, eu1, sfl]
    have e3 : talG H S (Function.update Ψ j (fun t => L * t)) σ =
        sSup ((fun h => u h + talSg (σ j) * (L * h (S j))) '' H) := by
      unfold talG; congr 2; funext h; rw [dec, eu2]; simp [hu]
    have e4 : talG H S (Function.update Ψ j (fun t => L * t)) (fl σ) =
        sSup ((fun h => u h + (- talSg (σ j)) * (L * h (S j))) '' H) := by
      unfold talG; congr 2; funext h; rw [dec, eu2, eu1, sfl]; simp
    rw [e1, e2, e3, e4]
    refine tal_key H u (fun h => h (S j)) (Ψ j) L (hΨ j) _ he
      (∑ i ∈ Finset.univ.erase j, (|Ψ i a| + L * (b - a))) a b ?_ (fun h hh => hHb h hh _)
    intro h hh
    calc |u h| ≤ ∑ i ∈ Finset.univ.erase j, |talSg (σ i) * Ψ i (h (S i))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
          apply Finset.sum_le_sum; intro i _
          rw [abs_mul]
          have : |talSg (σ i)| = 1 := by cases σ i <;> simp [talSg]
          rw [this, one_mul]
          exact tal_lipbd (Ψ i) L (hΨ i) a b _ (hHb h hh _)
  have h2 : 2 * ∑ σ, talG H S Ψ σ ≤ 2 * ∑ σ, talG H S (Function.update Ψ j (fun t => L * t)) σ := by
    calc 2 * ∑ σ, talG H S Ψ σ = ∑ σ, (talG H S Ψ σ + talG H S Ψ (fl σ)) := by
          rw [Finset.sum_add_distrib, hsum (talG H S Ψ)]; ring
      _ ≤ ∑ σ, (talG H S (Function.update Ψ j (fun t => L * t)) σ +
            talG H S (Function.update Ψ j (fun t => L * t)) (fl σ)) :=
          Finset.sum_le_sum (fun σ _ => pt σ)
      _ = _ := by rw [Finset.sum_add_distrib, hsum]; ring
  linarith

lemma tal_all {X : Type*} {m : ℕ} (H : Set (X → ℝ)) (S : Fin m → X) (a b : ℝ)
    (hHb : ∀ h ∈ H, ∀ x, h x ∈ Set.Icc a b) (Ψ : Fin m → ℝ → ℝ) (L : ℝ)
    (hΨ : ∀ i x y, |Ψ i x - Ψ i y| ≤ L * |x - y|) :
    ∑ σ, talG H S Ψ σ ≤ ∑ σ, talG H S (fun _ t => L * t) σ := by
  classical
  have : ∀ T : Finset (Fin m), ∑ σ, talG H S Ψ σ ≤
      ∑ σ, talG H S (fun i => if i ∈ T then (fun t => L * t) else Ψ i) σ := by
    intro T
    induction T using Finset.induction_on with
    | empty => simp
    | insert j T hjT ih =>
      refine ih.trans ?_
      have hΨ' : ∀ i x y, |(fun i => if i ∈ T then (fun t => L * t) else Ψ i) i x
          - (fun i => if i ∈ T then (fun t => L * t) else Ψ i) i y| ≤ L * |x - y| := by
        intro i x y
        have hL : 0 ≤ L := by
          have := hΨ i 1 0; norm_num at this; linarith [abs_nonneg (Ψ i 1 - Ψ i 0)]
        by_cases hi : i ∈ T
        · simp only [hi, if_true]; rw [← mul_sub, abs_mul, abs_of_nonneg hL]
        · simp only [hi, if_false]; exact hΨ i x y
      refine (tal_step H S a b hHb _ L hΨ' j).trans (le_of_eq ?_)
      congr 1; funext σ; congr 1; funext i
      by_cases hi : i = j
      · subst hi; simp
      · simp [Function.update_of_ne hi, Finset.mem_insert, hi]
  simpa using this Finset.univ

theorem talagrand_core {X : Type*} {m : ℕ} (H : Set (X → ℝ))
    (hHb : ∃ a b : ℝ, ∀ h ∈ H, ∀ x, h x ∈ Set.Icc a b) (S : Fin m → X)
    (Φ : Fin m → ℝ → ℝ) (l : ℝ) (hl : 0 ≤ l)
    (hLip : ∀ i : Fin m, ∀ x y : ℝ, |Φ i x - Φ i y| ≤ l * |x - y|) :
    (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
      sSup ((fun h : X → ℝ =>
        (1 / (m : ℝ)) * ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * Φ i (h (S i))) '' H)
      ≤ l * EmpiricalRademacherComplexity H S := by
  obtain ⟨a, b, hab⟩ := hHb
  have hm : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have hΨ : ∀ i x y, |(fun i t => (1 / (m : ℝ)) * Φ i t) i x - (fun i t => (1 / (m : ℝ)) * Φ i t) i y|
      ≤ (l / m) * |x - y| := by
    intro i x y
    simp only
    rw [← mul_sub, abs_mul, abs_of_nonneg hm]
    have := hLip i x y
    calc 1 / (m : ℝ) * |Φ i x - Φ i y| ≤ 1 / (m : ℝ) * (l * |x - y|) :=
          mul_le_mul_of_nonneg_left this hm
      _ = _ := by ring
  have key := tal_all H S a b hab _ (l / m) hΨ
  have eL : ∀ σ : Fin m → Bool, sSup ((fun h : X → ℝ =>
        (1 / (m : ℝ)) * ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * Φ i (h (S i))) '' H)
      = talG H S (fun i t => (1 / (m : ℝ)) * Φ i t) σ := by
    intro σ; unfold talG talSg; congr 2; funext h; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  have eR : ∀ σ : Fin m → Bool, talG H S (fun _ t => (l / m) * t) σ =
      l * sSup ((fun g : X → ℝ =>
        (1 / (m : ℝ)) * ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * g (S i)) '' H) := by
    intro σ
    rw [← smul_eq_mul, ← Real.sSup_smul_of_nonneg hl, ← Set.image_smul, Set.image_image]
    unfold talG talSg; congr 2; funext h; simp only [smul_eq_mul]; rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _; ring
  unfold EmpiricalRademacherComplexity
  simp_rw [eL]
  have : ∑ σ, talG H S (fun _ t => (l / m) * t) σ = l * ∑ σ : Fin m → Bool, sSup ((fun g : X → ℝ =>
        (1 / (m : ℝ)) * ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * g (S i)) '' H) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun σ _ => eR σ)
  have h2 : (0 : ℝ) ≤ 1 / 2 ^ m := by positivity
  calc 1 / (2 : ℝ) ^ m * ∑ σ, talG H S (fun i t => 1 / (m : ℝ) * Φ i t) σ
      ≤ 1 / (2 : ℝ) ^ m * ∑ σ, talG H S (fun _ t => (l / m) * t) σ :=
        mul_le_mul_of_nonneg_left key h2
    _ = _ := by rw [this]; ring

end FoundationsML.SVM

open FoundationsML.SVM


theorem solution {X : Type*} {m : ℕ} (H : Set (X → ℝ))
    (hHb : ∃ a b : ℝ, ∀ h ∈ H, ∀ x, h x ∈ Set.Icc a b) (S : Fin m → X)
    (Φ : Fin m → ℝ → ℝ) (l : ℝ) (hl : 0 ≤ l)
    (hLip : ∀ i : Fin m, ∀ x y : ℝ, |Φ i x - Φ i y| ≤ l * |x - y|) :
    (1 / (2 : ℝ) ^ m) * ∑ σ : Fin m → Bool,
      sSup ((fun h : X → ℝ =>
        (1 / (m : ℝ)) * ∑ i : Fin m, (if σ i then (1 : ℝ) else -1) * Φ i (h (S i))) '' H)
      ≤ l * EmpiricalRademacherComplexity H S := by
  exact talagrand_core H hHb S Φ l hl hLip
