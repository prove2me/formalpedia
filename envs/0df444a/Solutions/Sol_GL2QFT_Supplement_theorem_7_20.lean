-- Prove2me | solution 1 for GL2QFT.Supplement.theorem_7_20
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T03:34:04.980569+00:00
-- url     : https://prove2.me/submissions/95ec5c57-a745-4b7c-bc14-17f74eb94c23

import Definitions.Def_GL2QFT_Supplement_LittleGroup

noncomputable section

open Classical

section
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.LittleGroup

private theorem repEquiv_transport_iff {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (R₁ : N → Matrix ι₁ ι₁ ℂ) (R₂ : N → Matrix ι₂ ι₂ ℂ) (g : G) :
    RepEquiv (transport N R₁ g⁻¹) R₂ ↔ RepEquiv R₁ (transport N R₂ g) := by
  constructor
  · rintro ⟨A, B, hAB, hBA, h⟩
    refine ⟨A, B, hAB, hBA, fun n _ => ?_⟩
    let m : N := ⟨g⁻¹ * (n : G) * g, conj_inv_mem N g n⟩
    have hm := h m (Set.mem_univ _)
    have heq : transport N R₁ g⁻¹ m = R₁ n := by
      unfold transport
      congr 1; ext; simp [m, mul_assoc]
    rw [heq] at hm
    exact hm
  · rintro ⟨A, B, hAB, hBA, h⟩
    refine ⟨A, B, hAB, hBA, fun n _ => ?_⟩
    let m : N := ⟨g * (n : G) * g⁻¹, by simpa using (inferInstance : N.Normal).conj_mem n n.2 g⟩
    have hm := h m (Set.mem_univ _)
    have heq : transport N R₂ g m = R₂ n := by
      unfold transport
      congr 1; ext; simp [m, mul_assoc]
    rw [heq] at hm
    simpa [transport, m, mul_assoc] using hm

private theorem repEquiv_transport_transport_iff {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (l : ΛN) (t g : G) :
    RepEquiv (transport N (RN l) t) (transport N (RN l) g) ↔ t⁻¹ * g ∈ inertia N RN l := by
  have h1 : transport N (transport N (RN l) t) g⁻¹ = transport N (RN l) (g⁻¹ * t) := by
    funext n
    unfold transport
    congr 1
    ext
    simp [mul_assoc]
  have hiff : RepEquiv (transport N (RN l) t) (transport N (RN l) g) ↔
      g⁻¹ * t ∈ inertia N RN l := by
    change RepEquiv (transport N (RN l) t) (transport N (RN l) g) ↔
      RepEquiv (transport N (RN l) (g⁻¹ * t)) (RN l)
    rw [← h1]
    exact (repEquiv_transport_iff N (transport N (RN l) t) (RN l) g).symm
  rw [hiff]
  constructor
  · intro h
    have hi := (inertia N RN l).inv_mem h
    simpa [mul_assoc] using hi
  · intro h
    have hi := (inertia N RN l).inv_mem h
    simpa [mul_assoc] using hi

private theorem mem_inertia_of_mem_normal {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (l : ΛN) (hR : IsMatRep (RN l))
    (n₀ : N) : (n₀ : G) ∈ inertia N RN l := by
  have hmul_inv : RN l n₀ * RN l n₀⁻¹ = 1 := by
    rw [← hR.2, mul_inv_cancel, hR.1]
  have hinv_mul : RN l n₀⁻¹ * RN l n₀ = 1 := by
    rw [← hR.2, inv_mul_cancel, hR.1]
  refine ⟨RN l n₀, RN l n₀⁻¹, hmul_inv, hinv_mul, fun n _ => ?_⟩
  unfold transport
  have heq : (⟨(n₀ : G)⁻¹ * (n : G) * (n₀ : G), conj_inv_mem N (n₀ : G) n⟩ : N) =
      n₀⁻¹ * n * n₀ := by ext; rfl
  rw [heq, hR.2, hR.2]
  calc
    RN l n₀ * (RN l n₀⁻¹ * RN l n * RN l n₀) =
        (RN l n₀ * RN l n₀⁻¹) * RN l n * RN l n₀ := by simp only [Matrix.mul_assoc]
    _ = RN l n * RN l n₀ := by rw [hmul_inv, Matrix.one_mul]

private theorem card_eq_of_repEquiv {G ι κ : Type} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] {R₁ : G → Matrix ι ι ℂ} {R₂ : G → Matrix κ κ ℂ}
    (h : RepEquiv R₁ R₂) : Fintype.card ι = Fintype.card κ := by
  obtain ⟨A, B, hAB, hBA, _⟩ := h
  have htr : (Fintype.card κ : ℂ) = (Fintype.card ι : ℂ) := by
    calc
      (Fintype.card κ : ℂ) = Matrix.trace (1 : Matrix κ κ ℂ) := by simp
      _ = Matrix.trace (A * B) := by rw [hAB]
      _ = Matrix.trace (B * A) := Matrix.trace_mul_comm A B
      _ = Matrix.trace (1 : Matrix ι ι ℂ) := by rw [hBA]
      _ = (Fintype.card ι : ℂ) := by simp
  exact Nat.cast_injective htr.symm

theorem solution {G : Type} [Group G] [Fintype G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} [Fintype ΛN] (BN : ΛN → Type) [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (O : Set ΛN) (hO : IsOrbitTransversal N RN O)
    (Tσ : ΛN → Set G) (hTσ : ∀ σ ∈ O, IsLabelTransversal N BN RN Tσ σ)
    (U : ∀ σ : ΛN, G → ∀ l : ΛN, Matrix (BN l) (BN σ) ℂ)
    (hU : IsOrbitTransport N BN RN O Tσ U)
    (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
    (hext : ∀ l, IsExtension N RN l (Rext l))
    {Λη : ΛN → Type} [∀ σ, Fintype (Λη σ)] (Bη : ∀ σ, Λη σ → Type) [∀ σ η, Fintype (Bη σ η)]
    [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) →
      Matrix (Bη σ η) (Bη σ η) ℂ)
    (hRη : ∀ σ ∈ O, IsIrrepSystem (Rη σ))
    (TN : Set G) (hTN : Subgroup.IsComplement (N : Set G) TN)
    (l σ : ΛN) (tL : Tσ σ) (henc : IsOrbEnc N BN RN O Tσ l σ (tL : G)) :
    stepsRight N BN RN Tσ U Rext Bη Rη TN l σ tL =
      uIndRight N BN RN Tσ U Rext Bη Rη TN l σ tL := by
  let _ := hO
  let _ := hU
  let _ := hext
  let _ := hRη
  obtain ⟨hσ, _, hequiv⟩ := henc
  have hBN_card : Fintype.card (BN l) = Fintype.card (BN σ) :=
    card_eq_of_repEquiv hequiv
  have hTσ_σ : IsLabelTransversal N BN RN Tσ σ := hTσ σ hσ
  have hbij : Function.Bijective (fun p : Tσ σ × inertia N RN σ => (p.1 : G) * (p.2 : G)) := by
    rw [Function.bijective_iff_existsUnique]
    intro g
    obtain ⟨t, ht, huniq⟩ := hTσ_σ.2 g
    have hmem : (t : G)⁻¹ * g ∈ inertia N RN σ :=
      (repEquiv_transport_transport_iff N RN σ (t : G) g).mp ht
    refine ⟨(t, ⟨(t : G)⁻¹ * g, hmem⟩), ?_, ?_⟩
    · simp
    · rintro ⟨t', k'⟩ hk'
      have hk'_eq : (t' : G)⁻¹ * g = (k' : G) := by
        rw [← hk']
        simp
      have hmem' : (t' : G)⁻¹ * g ∈ inertia N RN σ := by
        rw [hk'_eq]
        exact k'.2
      have ht' : RepEquiv (transport N (RN σ) (t' : G)) (transport N (RN σ) g) :=
        (repEquiv_transport_transport_iff N RN σ (t' : G) g).mpr hmem'
      have htt' : t' = t := huniq t' ht'
      subst htt'
      ext
      · rfl
      · exact hk'_eq.symm
  have hcard_TI : Fintype.card (Tσ σ) * Fintype.card (inertia N RN σ) = Fintype.card G := by
    have he := Fintype.card_congr (Equiv.ofBijective _ hbij)
    simpa [Fintype.card_prod] using he
  have hcard_NT : Fintype.card N * Fintype.card TN = Fintype.card G := by
    have hc := hTN.card_mul_card
    simpa [Nat.card_eq_fintype_card] using hc
  have hN_le : N ≤ inertia N RN σ := fun x hx =>
    mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 ⟨x, hx⟩
  have hcard_sub : Fintype.card (N.subgroupOf (inertia N RN σ)) = Fintype.card N := by
    refine Fintype.card_congr ?_
    exact
      { toFun := fun x => ⟨(x.1 : G), x.2⟩
        invFun := fun y => ⟨⟨y.1, hN_le y.2⟩, y.2⟩
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
  have hcard_quot :
      Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) * Fintype.card N =
        Fintype.card (inertia N RN σ) := by
    have hq := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (inertia N RN σ))
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      hcard_sub] at hq
    exact hq.symm
  have hTN_eq : Fintype.card TN =
      Fintype.card (Tσ σ) * Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) := by
    have hN_pos : 0 < Fintype.card N := Fintype.card_pos_iff.mpr ⟨1⟩
    apply Nat.eq_of_mul_eq_mul_left hN_pos
    calc
      Fintype.card N * Fintype.card TN = Fintype.card G := hcard_NT
      _ = Fintype.card (Tσ σ) * Fintype.card (inertia N RN σ) := hcard_TI.symm
      _ = Fintype.card (Tσ σ) *
            (Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) * Fintype.card N) := by
          rw [hcard_quot]
      _ = Fintype.card N *
            (Fintype.card (Tσ σ) *
              Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ))) := by ring
  ext o kh
  rcases o with ⟨η, j, tR, kσ, lη⟩
  rcases kh with ⟨kl, h⟩
  simp only [stepsRight, uIndRight, littleRep, indRep, inflation, Matrix.of_apply]
  by_cases hm : (tL : G)⁻¹ * (h : G) * (tR : G) ∈ inertia N RN σ
  · rw [dif_pos hm]
    have hsqrt :
        (Real.sqrt ((Fintype.card (LBas BN Tσ Bη σ η) : ℝ) /
            ((Fintype.card (BN l) : ℝ) * (Fintype.card TN : ℝ))) : ℂ) =
          (Real.sqrt ((Fintype.card (Bη σ η) : ℝ) /
            (Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) : ℝ)) : ℂ) := by
      congr 2
      have hLBas : Fintype.card (LBas BN Tσ Bη σ η) =
          Fintype.card (Tσ σ) * (Fintype.card (BN σ) * Fintype.card (Bη σ η)) := by
        simp [LBas, Fintype.card_prod]
      have hTσ_pos : (0 : ℝ) < Fintype.card (Tσ σ) :=
        Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨tR⟩)
      have hBNσ_pos : (0 : ℝ) < Fintype.card (BN σ) :=
        Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨kσ⟩)
      have hH_pos : (0 : ℝ) < Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) :=
        Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨1⟩)
      rw [hLBas, hBN_card, hTN_eq]
      push_cast
      field_simp
    rw [hsqrt, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [dif_pos hm]
    dsimp only [Matrix.kronecker]
    rw [Matrix.kroneckerMap_apply]
    ring
  · rw [dif_neg hm]
    symm
    refine mul_eq_zero_of_right _ ?_
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [dif_neg hm, mul_zero]

end
