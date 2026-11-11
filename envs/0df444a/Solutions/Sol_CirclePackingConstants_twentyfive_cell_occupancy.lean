-- Prove2me | solution 1 for CirclePackingConstants.twentyfive_cell_occupancy
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @parclytaxel
-- created : 2026-11-10T17:59:17.409895+00:00
-- url     : https://prove2.me/submissions/5617ff2f-c43a-4fc4-94a8-45344ae7abc7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_CirclePackingConstants_twentyfive_missing_cell_halfbox_bound

noncomputable section

open CirclePackingConstants

private lemma fifth_interval (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ∃ a : Fin 5, (a.val : ℝ) / 5 ≤ x ∧ x ≤ ((a.val : ℝ) + 1) / 5 := by
  by_cases ha : x ≤ 1 / 5
  · exact ⟨0, by norm_num; exact ⟨h0, ha⟩⟩
  by_cases hb : x ≤ 2 / 5
  · exact ⟨1, by norm_num; constructor <;> linarith⟩
  by_cases hc : x ≤ 3 / 5
  · exact ⟨2, by norm_num; constructor <;> linarith⟩
  by_cases hd : x ≤ 4 / 5
  · exact ⟨3, by norm_num; constructor <;> linarith⟩
  exact ⟨4, by norm_num; constructor <;> linarith⟩

private lemma half_interval (y a : ℝ) (h : a ≤ y ∧ y ≤ a + 1 / 5) :
    ∃ b : Fin 2, a + (b.val : ℝ) / 10 ≤ y ∧
      y ≤ a + ((b.val : ℝ) + 1) / 10 := by
  by_cases hb : y ≤ a + 1 / 10
  · exact ⟨0, by norm_num; exact ⟨h.1, hb⟩⟩
  · exact ⟨1, by norm_num; constructor <;> linarith [h.2]⟩

private lemma halfbox_distance (p q : Point) (a b : ℝ)
    (hp : (a ≤ p.1 ∧ p.1 ≤ a + 1 / 5) ∧ (b ≤ p.2 ∧ p.2 ≤ b + 1 / 10))
    (hq : (a ≤ q.1 ∧ q.1 ≤ a + 1 / 5) ∧ (b ≤ q.2 ∧ q.2 ≤ b + 1 / 10)) :
    sqDist p q ≤ (1 : ℝ) / 20 := by
  have hx : (p.1 - q.1) ^ 2 ≤ (1 : ℝ) / 25 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 5 - (p.1 - q.1) by linarith [hp.1.2, hq.1.1])
      (show 0 ≤ 1 / 5 + (p.1 - q.1) by linarith [hp.1.1, hq.1.2])]
  have hy : (p.2 - q.2) ^ 2 ≤ (1 : ℝ) / 100 := by
    nlinarith [mul_nonneg (show 0 ≤ 1 / 10 - (p.2 - q.2) by linarith [hp.2.2, hq.2.1])
      (show 0 ≤ 1 / 10 + (p.2 - q.2) by linarith [hp.2.1, hq.2.2])]
  unfold sqDist
  linarith

theorem solution (p : Fin 25 → Point)
    (hp : ∀ i, 0 ≤ (p i).1 ∧ (p i).1 ≤ 1 ∧ 0 ≤ (p i).2 ∧ (p i).2 ≤ 1)
    (hd : ∀ i j, i ≠ j → (1 : ℝ) / 16 < sqDist (p i) (p j)) :
    ∃ σ : Fin 25 → Fin 5 × Fin 5, Function.Bijective σ ∧ ∀ k,
      ((σ k).1.val : ℝ) / 5 ≤ (p k).1 ∧ (p k).1 ≤ (((σ k).1.val : ℝ) + 1) / 5 ∧
      ((σ k).2.val : ℝ) / 5 ≤ (p k).2 ∧ (p k).2 ≤ (((σ k).2.val : ℝ) + 1) / 5 := by
  classical
  choose x hx using fun i ↦ fifth_interval (p i).1 (hp i).1 (hp i).2.1
  choose y hy using fun i ↦ fifth_interval (p i).2 (hp i).2.2.1 (hp i).2.2.2
  choose b hb using fun i ↦ half_interval (p i).2 ((y i).val / 5)
    ⟨(hy i).1, by linarith [(hy i).2]⟩
  let σ : Fin 25 → Fin 5 × Fin 5 := fun i ↦ (x i, y i)
  let τ : Fin 25 → (Fin 5 × Fin 5) × Fin 2 := fun i ↦ (σ i, b i)
  have hτ : Function.Injective τ := by
    intro i j hij
    by_contra hne
    have hxy := congrArg Prod.fst hij
    have hxx : x i = x j := congrArg Prod.fst hxy
    have hyy : y i = y j := congrArg Prod.snd hxy
    have hbb : b i = b j := congrArg Prod.snd hij
    have hclose := halfbox_distance (p i) (p j) ((x i).val / 5)
      ((y i).val / 5 + (b i).val / 10)
      ⟨⟨(hx i).1, by linarith [(hx i).2]⟩,
        ⟨(hb i).1, by linarith [(hb i).2]⟩⟩
      ⟨⟨by simpa [hxx] using (hx j).1, by rw [hxx]; linarith [(hx j).2]⟩,
        ⟨by simpa [hyy, hbb] using (hb j).1,
          by rw [hyy, hbb]; linarith [(hb j).2]⟩⟩
    linarith [hd i j hne]
  let S := Finset.univ.image τ
  let q := p ∘ Function.invFun τ
  have hq (i : Fin 25) : q (τ i) = p i := by
    exact congrArg p (Function.leftInverse_invFun hτ i)
  have hcard : S.card = 25 := by
    rw [Finset.card_image_of_injective _ hτ]
    simp
  have hsurj : Function.Surjective σ := by
    intro c
    by_contra hmissing
    have hempty : ∀ b : Fin 2, (c, b) ∉ S := by
      intro b hmem
      obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
      exact hmissing ⟨i, congrArg Prod.fst hi⟩
    have hbound := twentyfive_missing_cell_halfbox_bound S q (by
      intro r hr
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
      rw [hq]
      exact ⟨hx i, hb i⟩) (by
      intro r hr t ht hne
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hr
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
      rw [hq, hq]
      exact hd i j (fun hij ↦ hne (congrArg τ hij))) ⟨c, hempty⟩
    omega
  have hbij : Function.Bijective σ := by
    exact (Fintype.bijective_iff_surjective_and_card σ).2 ⟨hsurj, by decide⟩
  exact ⟨σ, hbij, fun i ↦ ⟨(hx i).1, (hx i).2, (hy i).1, (hy i).2⟩⟩
