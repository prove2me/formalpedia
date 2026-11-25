-- Prove2me | solution 1 for DetDLP.dense_covering_and_2m_decomp
-- status  : ACCEPTED   (prove)
-- author  : @Bingsheng
-- created : 2026-11-23T10:50:10.096764+00:00
-- url     : https://prove2.me/submissions/f4dd5be4-7bb9-4bde-93da-36de7200deae

import Mathlib
import Definitions.Def_DetDLP_FactorBase

set_option autoImplicit false

open DetDLP

private lemma dense_covering_and_2m_decomp_add
    {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {m : ℕ}
    (μ : ℝ) (F : Fin m → Finset G)
    (hμ : 0 < μ)
    (hΦ : collisionPotentialAdd μ F < (64 : ℝ) / 57) :
    7 * Fintype.card G ≤ 8 * (sumsetAdd F).card ∧
    ∀ X : G, ∃ A B : Fin m → G,
      (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
      (∑ i : Fin m, (A i + B i)) = X := by
  let D : Finset G := sumsetAdd F
  have hW_eq : (productSize F : ℝ) = ∑ g ∈ D, (repCountAdd F g : ℝ) := by
    have hnat : productSize F = ∑ g ∈ D, repCountAdd F g := by
      unfold productSize repCountAdd
      rw [← Fintype.card_piFinset]
      rw [Finset.card_eq_sum_card_fiberwise (f := fun A : Fin m → G => ∑ i : Fin m, A i)
        (s := Fintype.piFinset F) (t := D) (fun A hA => by
          simp only [D, sumsetAdd, Finset.mem_coe, Finset.mem_image]
          exact ⟨A, hA, rfl⟩)]
    exact_mod_cast hnat
  have hC_ge : ∑ g ∈ D, (repCountAdd F g : ℝ) ^ 2 ≤ (collisionEnergyAdd F : ℝ) := by
    unfold collisionEnergyAdd
    push_cast
    exact Finset.sum_le_univ_sum_of_nonneg fun _ => sq_nonneg _
  have hW_pos : 0 < (productSize F : ℝ) := by
    by_contra hle
    push Not at hle
    have hW0 : (productSize F : ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg _)
    unfold collisionPotentialAdd at hΦ
    rw [hW0] at hΦ
    have hCnn : (0 : ℝ) ≤ (Fintype.card G : ℝ) * (collisionEnergyAdd F : ℝ) := by positivity
    have hge : (64 : ℝ) ≤ ((Fintype.card G : ℝ) * (collisionEnergyAdd F : ℝ) + 64 * (0 - μ) ^ 2) / μ ^ 2 := by
      rw [le_div_iff₀ (pow_pos hμ 2)]
      nlinarith
    linarith
  have hD_pos : 0 < D.card := by
    by_contra h0
    have hDe : D = ∅ := Finset.card_eq_zero.mp (by omega)
    rw [hDe, Finset.sum_empty] at hW_eq
    linarith
  have hD_posR : (0 : ℝ) < (D.card : ℝ) := by exact_mod_cast hD_pos
  have hG_pos : 0 < Fintype.card G := lt_of_lt_of_le hD_pos (Finset.card_le_univ D)
  have hG_posR : (0 : ℝ) < (Fintype.card G : ℝ) := by exact_mod_cast hG_pos
  -- Cauchy-Schwarz: W^2 ≤ |D| * C_S
  have hCS : (productSize F : ℝ) ^ 2 ≤ (D.card : ℝ) * (collisionEnergyAdd F : ℝ) := by
    rw [hW_eq]
    have hcs := sq_sum_le_card_mul_sum_sq (s := D) (f := fun g => (repCountAdd F g : ℝ))
    exact le_trans hcs (mul_le_mul_of_nonneg_left hC_ge (le_of_lt hD_posR))
  -- Lower bound Φ(S) ≥ 64 / (64 δ + 1)
  let δ : ℝ := (D.card : ℝ) / (Fintype.card G : ℝ)
  let z : ℝ := (productSize F : ℝ) / μ
  have hδ_pos : 0 < δ := div_pos hD_posR hG_posR
  have hΦ_ge1 : z ^ 2 / δ + 64 * (z - 1) ^ 2 ≤ collisionPotentialAdd μ F := by
    unfold collisionPotentialAdd
    have hμ_ne : μ ≠ 0 := ne_of_gt hμ
    have hD_ne : (D.card : ℝ) ≠ 0 := ne_of_gt hD_posR
    have hG_ne : (Fintype.card G : ℝ) ≠ 0 := ne_of_gt hG_posR
    have hterm1 : z ^ 2 / δ ≤ (Fintype.card G : ℝ) * (collisionEnergyAdd F : ℝ) / μ ^ 2 := by
      dsimp only [z, δ]
      rw [div_pow, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
      field_simp [hμ_ne]
      nlinarith
    have hterm2 : 64 * (z - 1) ^ 2 = 64 * ((productSize F : ℝ) - μ) ^ 2 / μ ^ 2 := by
      dsimp only [z]; field_simp [hμ_ne]
    rw [add_div, ← hterm2]
    linarith
  have hmin : 64 / (64 * δ + 1) ≤ z ^ 2 / δ + 64 * (z - 1) ^ 2 := by
    have hden : 0 < 64 * δ + 1 := by linarith
    rw [div_le_iff₀ hden]
    have hsq : 0 ≤ ((64 * δ + 1) * z - 64 * δ) ^ 2 / δ := div_nonneg (sq_nonneg _) (le_of_lt hδ_pos)
    have hid : (z ^ 2 / δ + 64 * (z - 1) ^ 2) * (64 * δ + 1) - 64 =
        ((64 * δ + 1) * z - 64 * δ) ^ 2 / δ := by
      have hδ_ne : δ ≠ 0 := ne_of_gt hδ_pos
      field_simp [hδ_ne]
      ring
    linarith
  have hlt : 64 / (64 * δ + 1) < (64 : ℝ) / 57 := lt_of_le_of_lt (le_trans hmin hΦ_ge1) hΦ
  have hδ_gt : (7 : ℝ) / 8 < δ := by
    have hden : 0 < 64 * δ + 1 := by linarith
    rw [div_lt_div_iff₀ hden (by norm_num)] at hlt
    linarith
  have h78R : (7 : ℝ) * (Fintype.card G : ℝ) < 8 * (D.card : ℝ) := by
    dsimp only [δ] at hδ_gt
    rw [div_lt_div_iff₀ (by norm_num) hG_posR] at hδ_gt
    linarith
  have h78 : 7 * Fintype.card G ≤ 8 * D.card := by
    have hltN : 7 * Fintype.card G < 8 * D.card := by exact_mod_cast h78R
    omega
  refine ⟨h78, fun X => ?_⟩
  -- Pigeonhole: |D| + |X - D| = 2|D| > |G|, so D ∩ (X - D) is nonempty
  let Dshift : Finset G := D.image (fun d => X - d)
  have hDshift_card : Dshift.card = D.card := by
    refine Finset.card_image_of_injective D ?_
    intro a b hab
    exact sub_right_injective hab
  have h2D_gt : Fintype.card G < D.card + Dshift.card := by
    rw [hDshift_card]
    have hltN : 7 * Fintype.card G < 8 * D.card := by exact_mod_cast h78R
    omega
  have hinter : (D ∩ Dshift).Nonempty := by
    by_contra hemp
    rw [Finset.not_nonempty_iff_eq_empty] at hemp
    have hunion := Finset.card_union_add_card_inter D Dshift
    rw [hemp, Finset.card_empty, add_zero] at hunion
    have hle : (D ∪ Dshift).card ≤ Fintype.card G := Finset.card_le_univ _
    omega
  obtain ⟨y, hy⟩ := hinter
  rw [Finset.mem_inter] at hy
  obtain ⟨hyD, hyS⟩ := hy
  simp only [Dshift, Finset.mem_image] at hyS
  obtain ⟨zD, hzD, hyz⟩ := hyS
  simp only [D, sumsetAdd, Finset.mem_image, Fintype.mem_piFinset] at hyD hzD
  obtain ⟨A, hA, hAsum⟩ := hyD
  obtain ⟨B, hB, hBsum⟩ := hzD
  refine ⟨A, B, fun i => ⟨hA i, hB i⟩, ?_⟩
  rw [Finset.sum_add_distrib, hAsum, hBsum, ← hyz]
  abel

theorem solution :
    (∀ {G : Type} [AddCommGroup G] [Fintype G] [DecidableEq G] {m : ℕ}
        (μ : ℝ) (F : Fin m → Finset G),
      0 < μ →
      collisionPotentialAdd μ F < (64 : ℝ) / 57 →
      7 * Fintype.card G ≤ 8 * (sumsetAdd F).card ∧
      ∀ X : G, ∃ A B : Fin m → G,
        (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
        (∑ i : Fin m, (A i + B i)) = X) ∧
    (∀ {G : Type} [CommGroup G] [Fintype G] [DecidableEq G] {m : ℕ}
        (μ : ℝ) (F : Fin m → Finset G),
      0 < μ →
      collisionPotentialMul μ F < (64 : ℝ) / 57 →
      7 * Fintype.card G ≤ 8 * (prodsetMul F).card ∧
      ∀ X : G, ∃ A B : Fin m → G,
        (∀ i : Fin m, A i ∈ F i ∧ B i ∈ F i) ∧
        (∏ i : Fin m, (A i * B i)) = X) := by
  refine ⟨fun μ F hμ hΦ => dense_covering_and_2m_decomp_add μ F hμ hΦ, ?_⟩
  intro G _ _ _ m μ F hμ hΦ
  let Fa : Fin m → Finset (Additive G) := fun i => (F i).map Additive.ofMul.toEmbedding
  have hcardG : Fintype.card (Additive G) = Fintype.card G :=
    Fintype.card_congr Additive.toMul
  have hC : collisionEnergyAdd Fa = collisionEnergyMul F := by
    unfold collisionEnergyAdd collisionEnergyMul repCountAdd repCountMul
    refine (Fintype.sum_equiv Additive.ofMul _ _ fun g => ?_).symm
    refine congrArg (· ^ 2) ?_
    refine Finset.card_bij (fun A _ i => Additive.ofMul (A i)) ?_ ?_ ?_
    · intro A hA
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Fa, Finset.mem_map,
        Equiv.toEmbedding_apply] at hA ⊢
      exact ⟨fun i => ⟨A i, hA.1 i, rfl⟩, by simpa [ofMul_prod] using congrArg Additive.ofMul hA.2⟩
    · intro A₁ _ A₂ _ h
      funext i; exact Additive.ofMul.injective (congrFun h i)
    · intro A hA
      simp only [Finset.mem_filter, Fintype.mem_piFinset, Fa, Finset.mem_map,
        Equiv.toEmbedding_apply] at hA ⊢
      refine ⟨fun i => Additive.toMul (A i), ⟨fun i => ?_, ?_⟩, funext fun i => rfl⟩
      · obtain ⟨x, hx, hxa⟩ := hA.1 i
        simpa [← hxa] using hx
      · have := congrArg Additive.toMul hA.2
        simpa [toMul_sum] using this
  have hW : productSize Fa = productSize F := by
    unfold productSize
    refine Finset.prod_congr rfl fun i _ => ?_
    simp [Fa]
  have hΦa : collisionPotentialAdd μ Fa < (64 : ℝ) / 57 := by
    have heq : collisionPotentialAdd μ Fa = collisionPotentialMul μ F := by
      unfold collisionPotentialAdd collisionPotentialMul
      rw [hcardG, hC, hW]
    rw [heq]; exact hΦ
  obtain ⟨h78a, hdeca⟩ := dense_covering_and_2m_decomp_add μ Fa hμ hΦa
  have hsum_card : (sumsetAdd Fa).card = (prodsetMul F).card := by
    refine Finset.card_bij (fun x _ => Additive.toMul x) ?_ ?_ ?_
    · intro x hx
      simp only [sumsetAdd, prodsetMul, Finset.mem_image, Fintype.mem_piFinset, Fa, Finset.mem_map,
        Equiv.toEmbedding_apply] at hx ⊢
      obtain ⟨A, hA, rfl⟩ := hx
      refine ⟨fun i => Additive.toMul (A i), fun i => ?_, ?_⟩
      · obtain ⟨y, hy, hya⟩ := hA i; simpa [← hya] using hy
      · simp [toMul_sum]
    · intro x₁ _ x₂ _ h; exact Additive.toMul.injective h
    · intro y hy
      simp only [sumsetAdd, prodsetMul, Finset.mem_image, Fintype.mem_piFinset, Fa, Finset.mem_map,
        Equiv.toEmbedding_apply] at hy ⊢
      obtain ⟨A, hA, rfl⟩ := hy
      refine ⟨Additive.ofMul (∏ i : Fin m, A i), ⟨fun i => Additive.ofMul (A i),
        fun i => ⟨A i, hA i, rfl⟩, by simp [ofMul_prod]⟩, rfl⟩
  rw [hcardG, hsum_card] at h78a
  refine ⟨h78a, fun X => ?_⟩
  obtain ⟨Aa, Ba, hmem, hsum⟩ := hdeca (Additive.ofMul X)
  refine ⟨fun i => Additive.toMul (Aa i), fun i => Additive.toMul (Ba i), fun i => ?_, ?_⟩
  · have h1 := (hmem i).1
    have h2 := (hmem i).2
    simp only [Fa, Finset.mem_map, Equiv.toEmbedding_apply] at h1 h2
    obtain ⟨a, ha, hae⟩ := h1
    obtain ⟨b, hb, hbe⟩ := h2
    exact ⟨by simpa [← hae] using ha, by simpa [← hbe] using hb⟩
  · have := congrArg Additive.toMul hsum
    simpa [toMul_sum, toMul_add] using this
