-- Prove2me | solution 1 for GL2QFT.Supplement.theorem_7_21
-- status  : ACCEPTED   (prove)
-- author  : @dmitry
-- created : 2026-11-22T03:39:50.84137+00:00
-- url     : https://prove2.me/submissions/8f5ba917-f442-49fb-898f-b0d1e879c128

import Definitions.Def_GL2QFT_Supplement_LittleGroup

noncomputable section

open Classical
open scoped Matrix ComplexConjugate
open GL2QFT GL2QFT.Supplement GL2QFT.Supplement.LittleGroup

namespace GL2QFT.Supplement.Thm721Helpers

/-! ### Part 1: Equivalence, transport, inertia, and label transversals -/

private theorem repEquiv_refl {G ι : Type} [Fintype ι] [DecidableEq ι]
    (R : G → Matrix ι ι ℂ) : RepEquiv R R := by
  refine ⟨1, 1, Matrix.one_mul _, Matrix.one_mul _, fun g _ => ?_⟩
  rw [Matrix.one_mul, Matrix.mul_one]

private theorem repEquiv_symm {G ι₁ ι₂ : Type} [Fintype ι₁] [Fintype ι₂]
    [DecidableEq ι₁] [DecidableEq ι₂]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ}
    (h : RepEquiv R₁ R₂) : RepEquiv R₂ R₁ := by
  obtain ⟨A, B, hAB, hBA, hinter⟩ := h
  refine ⟨B, A, hBA, hAB, fun g hg => ?_⟩
  calc B * R₂ g = B * R₂ g * (A * B) := by rw [hAB, Matrix.mul_one]
    _ = B * (R₂ g * A) * B := by simp only [Matrix.mul_assoc]
    _ = B * (A * R₁ g) * B := by rw [hinter g hg]
    _ = (B * A) * R₁ g * B := by simp only [Matrix.mul_assoc]
    _ = R₁ g * B := by rw [hBA, Matrix.one_mul]

private theorem repEquiv_trans {G ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    [DecidableEq ι₁] [DecidableEq ι₂] [DecidableEq ι₃]
    {R₁ : G → Matrix ι₁ ι₁ ℂ} {R₂ : G → Matrix ι₂ ι₂ ℂ} {R₃ : G → Matrix ι₃ ι₃ ℂ}
    (h12 : RepEquiv R₁ R₂) (h23 : RepEquiv R₂ R₃) : RepEquiv R₁ R₃ := by
  obtain ⟨A₁, B₁, hAB₁, hBA₁, hi₁⟩ := h12
  obtain ⟨A₂, B₂, hAB₂, hBA₂, hi₂⟩ := h23
  refine ⟨A₂ * A₁, B₁ * B₂, ?_, ?_, fun g hg => ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc A₁, hAB₁, Matrix.one_mul, hAB₂]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc B₂, hBA₂, Matrix.one_mul, hBA₁]
  · rw [Matrix.mul_assoc, hi₁ g hg, ← Matrix.mul_assoc, hi₂ g hg, Matrix.mul_assoc]

private theorem transport_isMatRep {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : N → Matrix ι ι ℂ} (hR : IsMatRep R) (g : G) :
    IsMatRep (transport N R g) := by
  constructor
  · have h1 : (⟨g⁻¹ * ((1 : N) : G) * g, conj_inv_mem N g 1⟩ : N) = 1 := by ext; simp
    unfold transport
    rw [h1]
    exact hR.1
  · intro m n
    unfold transport
    have hmul : (⟨g⁻¹ * ((m * n : N) : G) * g, conj_inv_mem N g (m * n)⟩ : N) =
        ⟨g⁻¹ * (m : G) * g, conj_inv_mem N g m⟩ * ⟨g⁻¹ * (n : G) * g, conj_inv_mem N g n⟩ := by
      ext; simp [mul_assoc]
    rw [hmul, hR.2]

private theorem transport_isIrreducibleRep {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ι : Type} [Fintype ι]
    {R : N → Matrix ι ι ℂ} (hR : IsIrreducibleRep R) (g : G) :
    IsIrreducibleRep (transport N R g) := by
  refine ⟨hR.1, fun W hW => hR.2 W fun n v hv => ?_⟩
  let m : N := ⟨g * (n : G) * g⁻¹, by simpa using (inferInstance : N.Normal).conj_mem n n.2 g⟩
  have heq : transport N R g m = R n := by
    unfold transport
    congr 1; ext; simp [m, mul_assoc]
  rw [← heq]
  exact hW m v hv

private theorem mem_inertia_of_mem_normal {G : Type} [Group G] (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (l : ΛN) (hR : IsMatRep (RN l))
    (n₀ : N) : (n₀ : G) ∈ inertia N RN l := by
  have h1 : RN l n₀ * RN l n₀⁻¹ = 1 := by rw [← hR.2, mul_inv_cancel, hR.1]
  have h2 : RN l n₀⁻¹ * RN l n₀ = 1 := by rw [← hR.2, inv_mul_cancel, hR.1]
  refine ⟨RN l n₀, RN l n₀⁻¹, h1, h2, fun n _ => ?_⟩
  unfold transport
  have heq : (⟨(n₀ : G)⁻¹ * (n : G) * (n₀ : G), conj_inv_mem N (n₀ : G) n⟩ : N) =
      n₀⁻¹ * n * n₀ := by ext; rfl
  rw [heq, hR.2, hR.2, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul]

private theorem repEquiv_transport_iff_inv_mul_mem_inertia {G : Type} [Group G]
    (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (σ : ΛN) (t g : G) :
    RepEquiv (transport N (RN σ) t) (transport N (RN σ) g) ↔ t⁻¹ * g ∈ inertia N RN σ := by
  constructor
  · intro h
    obtain ⟨A, B, hAB, hBA, hinter⟩ := h
    apply repEquiv_symm
    refine ⟨A, B, hAB, hBA, fun m _ => ?_⟩
    let n : N := ⟨t * (m : G) * t⁻¹, by simpa using (inferInstance : N.Normal).conj_mem m m.2 t⟩
    have hn := hinter n (Set.mem_univ _)
    have e1 : transport N (RN σ) t n = RN σ m := by
      unfold transport; congr 1; ext; simp [n, mul_assoc]
    have e2 : transport N (RN σ) g n = transport N (RN σ) (t⁻¹ * g) m := by
      unfold transport; congr 1; ext; simp [n, mul_assoc]
    rw [e1, e2] at hn
    exact hn
  · intro hmem
    obtain ⟨A, B, hAB, hBA, hinter⟩ := repEquiv_symm hmem
    refine ⟨A, B, hAB, hBA, fun n _ => ?_⟩
    let m : N := ⟨t⁻¹ * (n : G) * t, conj_inv_mem N t n⟩
    have hm := hinter m (Set.mem_univ _)
    have e1 : RN σ m = transport N (RN σ) t n := rfl
    have e2 : transport N (RN σ) (t⁻¹ * g) m = transport N (RN σ) g n := by
      unfold transport; congr 1; ext; simp [m, mul_assoc]
    rw [e1, e2] at hm
    exact hm

private theorem isComplement_of_isLabelTransversal {G : Type} [Group G]
    (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (Tσ : ΛN → Set G) (σ : ΛN)
    (hT : IsLabelTransversal N BN RN Tσ σ) :
    Subgroup.IsComplement (Tσ σ) (inertia N RN σ : Set G) := by
  rw [Subgroup.IsComplement, Function.bijective_iff_existsUnique]
  intro g
  obtain ⟨t, ht, huniq⟩ := hT.2 g
  have htk : (t : G)⁻¹ * g ∈ inertia N RN σ :=
    (repEquiv_transport_iff_inv_mul_mem_inertia N RN σ (t : G) g).mp ht
  refine ⟨⟨t, ⟨(t : G)⁻¹ * g, htk⟩⟩, by simp, ?_⟩
  rintro ⟨t', k'⟩ hmul
  have ht'g : (t' : G)⁻¹ * g ∈ inertia N RN σ := by
    have hk' : (k' : G) = (t' : G)⁻¹ * g := by
      calc (k' : G) = (t' : G)⁻¹ * ((t' : G) * (k' : G)) := by simp
        _ = (t' : G)⁻¹ * g := by rw [hmul]
    rw [← hk']
    exact k'.2
  have ht'_eq : t' = t :=
    huniq t' ((repEquiv_transport_iff_inv_mul_mem_inertia N RN σ (t' : G) g).mpr ht'g)
  ext1
  · exact ht'_eq
  · ext1
    have hmul' : (t : G) * (k' : G) = (t : G) * ((t : G)⁻¹ * g) := by
      calc (t : G) * (k' : G) = (t' : G) * (k' : G) := by rw [ht'_eq]
        _ = g := hmul
        _ = (t : G) * ((t : G)⁻¹ * g) := by simp
    exact mul_left_cancel hmul'

private theorem eq_of_inv_mul_mem_inertia {G : Type} [Group G]
    (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (Tσ : ΛN → Set G) (σ : ΛN)
    (hT : IsLabelTransversal N BN RN Tσ σ)
    {t₁ t₂ : Tσ σ} (hmem : (t₁ : G)⁻¹ * (t₂ : G) ∈ inertia N RN σ) : t₁ = t₂ := by
  obtain ⟨t, _, huniq⟩ := hT.2 (t₂ : G)
  have h1 : t₁ = t :=
    huniq t₁ ((repEquiv_transport_iff_inv_mul_mem_inertia N RN σ (t₁ : G) (t₂ : G)).mpr hmem)
  have h2 : t₂ = t :=
    huniq t₂ ((repEquiv_transport_iff_inv_mul_mem_inertia N RN σ (t₂ : G) (t₂ : G)).mpr
      (by simp [(inertia N RN σ).one_mem]))
  exact h1.trans h2.symm

/-! ### Part 2: Cardinality helpers and Theorem 7.20 (`stepsRight = uIndRight`) -/

private theorem card_eq_of_unitary {α β : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    (A : Matrix α β ℂ) (B : Matrix β α ℂ) (hAB : A * B = 1) (hBA : B * A = 1) :
    Fintype.card α = Fintype.card β := by
  have h : (A * B).trace = (B * A).trace := Matrix.trace_mul_comm A B
  rw [hAB, hBA, Matrix.trace_one, Matrix.trace_one] at h
  exact Nat.cast_inj.mp h

private theorem card_inertia_quotient_mul_card_N {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (σ : ΛN)
    (hN_le : ∀ n : N, (n : G) ∈ inertia N RN σ) :
    Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) * Fintype.card N =
      Fintype.card (inertia N RN σ) := by
  have hLag := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf (inertia N RN σ))
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hLag
  have hsub : Fintype.card (N.subgroupOf (inertia N RN σ)) = Fintype.card N := by
    refine Fintype.card_congr ?_
    exact
      { toFun := fun x => ⟨((x : inertia N RN σ) : G), x.2⟩
        invFun := fun n => ⟨⟨n.1, hN_le n⟩, n.2⟩
        left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
        right_inv := fun ⟨_, _⟩ => rfl }
  rw [hsub] at hLag
  exact hLag.symm

private theorem stepsRight_eq_uIndRight {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal]
    {ΛN : Type} [Fintype ΛN] (BN : ΛN → Type) [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (O : Set ΛN)
    (Tσ : ΛN → Set G) (hTσ : ∀ σ ∈ O, IsLabelTransversal N BN RN Tσ σ)
    (U : ∀ σ : ΛN, G → ∀ l : ΛN, Matrix (BN l) (BN σ) ℂ)
    (hU : IsOrbitTransport N BN RN O Tσ U)
    (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
    {Λη : ΛN → Type} [∀ σ, Fintype (Λη σ)] (Bη : ∀ σ, Λη σ → Type) [∀ σ η, Fintype (Bη σ η)]
    [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) →
      Matrix (Bη σ η) (Bη σ η) ℂ)
    (TN : Set G) (hTN : Subgroup.IsComplement (N : Set G) TN)
    (l σ : ΛN) (tL : Tσ σ) (henc : IsOrbEnc N BN RN O Tσ l σ (tL : G)) :
    stepsRight N BN RN Tσ U Rext Bη Rη TN l σ tL =
      uIndRight N BN RN Tσ U Rext Bη Rη TN l σ tL := by
  ext o kh
  rcases o with ⟨η, j, tR, kσ, lη⟩
  simp only [stepsRight, uIndRight, littleRep, indRep, inflation, Matrix.of_apply]
  by_cases hm : (tL : G)⁻¹ * (kh.2 : G) * (tR : G) ∈ inertia N RN σ
  · rw [dif_pos hm]
    have hsum_eq :
        ∑ i : BN σ, U σ (tL : G) l kh.1 i *
            (if h : (tL : G)⁻¹ * (kh.2 : G) * (tR : G) ∈ inertia N RN σ then
              Matrix.kronecker (Rext σ ⟨_, h⟩)
                (Rη σ η (QuotientGroup.mk ⟨_, h⟩)) (i, j) (kσ, lη)
            else 0) =
          (∑ k'' : BN σ, U σ (tL : G) l kh.1 k'' * Rext σ ⟨_, hm⟩ k'' kσ) *
            Rη σ η (QuotientGroup.mk ⟨_, hm⟩) j lη := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [dif_pos hm, Matrix.kronecker, Matrix.kronecker_apply]
      ring
    rw [hsum_eq]
    have hsum_factor :
        ∑ k'' : BN σ, U σ (tL : G) l kh.1 k'' * Rext σ ⟨_, hm⟩ k'' kσ *
            ((Real.sqrt ((Fintype.card (Bη σ η) : ℝ) /
              (Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) : ℝ)) : ℂ) *
              Rη σ η (QuotientGroup.mk ⟨_, hm⟩) j lη) =
          (Real.sqrt ((Fintype.card (Bη σ η) : ℝ) /
              (Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) : ℝ)) : ℂ) *
            ((∑ k'' : BN σ, U σ (tL : G) l kh.1 k'' * Rext σ ⟨_, hm⟩ k'' kσ) *
              Rη σ η (QuotientGroup.mk ⟨_, hm⟩) j lη) := by
      rw [Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k'' _ => ?_
      ring
    rw [hsum_factor]
    congr 1
    have hU_unit := hU.2 l σ (tL : G) henc
    have hd_eq : Fintype.card (BN l) = Fintype.card (BN σ) :=
      card_eq_of_unitary (U σ (tL : G) l) (U σ (tL : G) l)ᴴ hU_unit.1 hU_unit.2.1
    have hc_NTN : Fintype.card N * Fintype.card TN = Fintype.card G := by
      have hc := hTN.card_mul_card
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hc
      exact hc
    have hcompl_Tσ : Subgroup.IsComplement (Tσ σ) (inertia N RN σ : Set G) :=
      isComplement_of_isLabelTransversal N RN Tσ σ (hTσ σ henc.1)
    have hc_TσI : Fintype.card (Tσ σ) * Fintype.card (inertia N RN σ) = Fintype.card G := by
      have hc := hcompl_Tσ.card_mul_card
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hc
      exact hc
    have hc_HI :
        Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) * Fintype.card N =
          Fintype.card (inertia N RN σ) :=
      card_inertia_quotient_mul_card_N N RN σ (mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1)
    have hc_LBas :
        Fintype.card (LBas BN Tσ Bη σ η) =
          Fintype.card (Tσ σ) * (Fintype.card (BN σ) * Fintype.card (Bη σ η)) := by
      rw [Fintype.card_prod, Fintype.card_prod]
    have hBNl_pos : (0 : ℝ) < Fintype.card (BN l) :=
      Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨kh.1⟩)
    have hTσ_pos : (0 : ℝ) < Fintype.card (Tσ σ) :=
      Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨tL⟩)
    have hH_pos : (0 : ℝ) < Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) :=
      Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨1⟩)
    congr 1
    congr 1
    have h1 : (Fintype.card (LBas BN Tσ Bη σ η) : ℝ) =
        (Fintype.card (Tσ σ) : ℝ) * ((Fintype.card (BN σ) : ℝ) * (Fintype.card (Bη σ η) : ℝ)) := by
      exact_mod_cast hc_LBas
    have h2 : (Fintype.card (BN σ) : ℝ) = (Fintype.card (BN l) : ℝ) := by
      exact_mod_cast hd_eq.symm
    have h3_nat : Fintype.card (Tσ σ) *
        Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) = Fintype.card TN := by
      apply Nat.eq_of_mul_eq_mul_right (Fintype.card_pos_iff.mpr ⟨(1 : N)⟩)
      calc Fintype.card (Tσ σ) *
              Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) * Fintype.card N
          = Fintype.card (Tσ σ) * Fintype.card (inertia N RN σ) := by rw [mul_assoc, hc_HI]
        _ = Fintype.card G := hc_TσI
        _ = Fintype.card N * Fintype.card TN := hc_NTN.symm
        _ = Fintype.card TN * Fintype.card N := mul_comm _ _
    have h3 : (Fintype.card (Tσ σ) : ℝ) *
        (Fintype.card (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) : ℝ) =
        (Fintype.card TN : ℝ) := by
      exact_mod_cast h3_nat
    rw [h1, h2, ← h3]
    field_simp
  · rw [dif_neg hm]
    symm
    rw [mul_eq_zero]
    right
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [dif_neg hm, mul_zero]

/-! ### Part 3: Multiplicativity and normal-subgroup action of `littleRep` -/

private theorem indRep_mul {G : Type} [Group G] (K : Subgroup G) (T : Set G) [Fintype T]
    (hT : Subgroup.IsComplement T (K : Set G)) {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : K → Matrix ι ι ℂ} (hR : IsMatRep R) (g₁ g₂ : G) :
    indRep K T R (g₁ * g₂) = indRep K T R g₁ * indRep K T R g₂ := by
  ext ⟨s, j⟩ ⟨t, i⟩
  simp only [indRep, Matrix.mul_apply, Matrix.of_apply, Fintype.sum_prod_type]
  obtain ⟨⟨u₀, k₀⟩, huk₀, huniq⟩ := hT.existsUnique (g₂ * (t : G))
  have huk₀' : (u₀ : G) * (k₀ : G) = g₂ * (t : G) := huk₀
  have hu₀_mem : (u₀ : G)⁻¹ * g₂ * (t : G) ∈ K := by
    have heq : (u₀ : G)⁻¹ * g₂ * (t : G) = (k₀ : G) := by
      calc (u₀ : G)⁻¹ * g₂ * (t : G) = (u₀ : G)⁻¹ * (g₂ * (t : G)) := by rw [mul_assoc]
        _ = (u₀ : G)⁻¹ * ((u₀ : G) * (k₀ : G)) := by rw [← huk₀']
        _ = (k₀ : G) := by simp
    rw [heq]
    exact k₀.2
  have hiff : ∀ u : T, (u : G)⁻¹ * g₂ * (t : G) ∈ K ↔ u = u₀ := by
    intro u
    constructor
    · intro hu
      have hmul : (u : G) * ((u : G)⁻¹ * g₂ * (t : G)) = g₂ * (t : G) := by
        simp [mul_assoc]
      have hp := huniq ⟨u, ⟨(u : G)⁻¹ * g₂ * (t : G), hu⟩⟩ hmul
      exact congrArg Prod.fst hp
    · rintro rfl
      exact hu₀_mem
  have hsum_u :
      ∑ u : T, ∑ k : ι,
          (if h : (s : G)⁻¹ * g₁ * (u : G) ∈ K then R ⟨_, h⟩ j k else 0) *
            (if h : (u : G)⁻¹ * g₂ * (t : G) ∈ K then R ⟨_, h⟩ k i else 0) =
        ∑ k : ι,
          (if h : (s : G)⁻¹ * g₁ * (u₀ : G) ∈ K then R ⟨_, h⟩ j k else 0) *
            R ⟨_, hu₀_mem⟩ k i := by
    refine (Finset.sum_eq_single u₀ ?_ fun hmem => absurd (Finset.mem_univ _) hmem).trans ?_
    · intro u _ hne
      refine Finset.sum_eq_zero fun k _ => ?_
      have hnot : ¬ (u : G)⁻¹ * g₂ * (t : G) ∈ K := fun hu => hne ((hiff u).mp hu)
      rw [dif_neg hnot, mul_zero]
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [dif_pos hu₀_mem]
  rw [hsum_u]
  have hK_iff : (s : G)⁻¹ * (g₁ * g₂) * (t : G) ∈ K ↔ (s : G)⁻¹ * g₁ * (u₀ : G) ∈ K := by
    have heq : (s : G)⁻¹ * (g₁ * g₂) * (t : G) = ((s : G)⁻¹ * g₁ * (u₀ : G)) * (k₀ : G) := by
      calc (s : G)⁻¹ * (g₁ * g₂) * (t : G)
          = (s : G)⁻¹ * g₁ * (g₂ * (t : G)) := by simp only [mul_assoc]
        _ = (s : G)⁻¹ * g₁ * ((u₀ : G) * (k₀ : G)) := by rw [← huk₀']
        _ = ((s : G)⁻¹ * g₁ * (u₀ : G)) * (k₀ : G) := by simp only [mul_assoc]
    rw [heq]
    exact K.mul_mem_cancel_right k₀.2
  by_cases h1 : (s : G)⁻¹ * g₁ * (u₀ : G) ∈ K
  · have h12 : (s : G)⁻¹ * (g₁ * g₂) * (t : G) ∈ K := hK_iff.mpr h1
    rw [dif_pos h12]
    have hk_eq : (⟨(s : G)⁻¹ * (g₁ * g₂) * (t : G), h12⟩ : K) =
        ⟨(s : G)⁻¹ * g₁ * (u₀ : G), h1⟩ * ⟨(u₀ : G)⁻¹ * g₂ * (t : G), hu₀_mem⟩ := by
      ext; simp [mul_assoc]
    rw [hk_eq, hR.2, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [dif_pos h1]
  · have h12 : ¬ (s : G)⁻¹ * (g₁ * g₂) * (t : G) ∈ K := fun h => h1 (hK_iff.mp h)
    rw [dif_neg h12]
    symm
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [dif_neg h1, zero_mul]

private theorem littleRep_mul {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ)
    (O : Set ΛN)
    (Tσ : ΛN → Set G) (hTσ : ∀ σ ∈ O, IsLabelTransversal N BN RN Tσ σ)
    (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
    (hext : ∀ l, IsExtension N RN l (Rext l))
    {Λη : ΛN → Type} {Bη : ∀ σ, Λη σ → Type} [∀ σ η, Fintype (Bη σ η)]
    [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) →
      Matrix (Bη σ η) (Bη σ η) ℂ)
    (hRη : ∀ σ ∈ O, IsIrrepSystem (Rη σ))
    {σ : ΛN} (hσO : σ ∈ O) (η : Λη σ) (g₁ g₂ : G) :
    littleRep N BN RN Tσ Rext Bη Rη σ η (g₁ * g₂) =
      littleRep N BN RN Tσ Rext Bη Rη σ η g₁ * littleRep N BN RN Tσ Rext Bη Rη σ η g₂ := by
  have hcompl := isComplement_of_isLabelTransversal N RN Tσ σ (hTσ σ hσO)
  have hR_mat : IsMatRep (fun k : inertia N RN σ =>
      Matrix.kronecker (Rext σ k) (inflation N RN σ (Rη σ η) k)) := by
    constructor
    · simp [(hext σ).1.1.1, inflation, QuotientGroup.mk_one, ((hRη σ hσO).1 η).1.1]
    · intro k₁ k₂
      simp [(hext σ).1.1.2, inflation, QuotientGroup.mk_mul, ((hRη σ hσO).1 η).1.2,
        Matrix.mul_kronecker_mul]
  exact indRep_mul (inertia N RN σ) (Tσ σ) hcompl hR_mat g₁ g₂

private theorem littleRep_mem_normal {G : Type} [Group G] [Fintype G]
    (N : Subgroup G) [N.Normal]
    {ΛN : Type} {BN : ΛN → Type} [∀ l, Fintype (BN l)] [∀ l, DecidableEq (BN l)]
    (RN : ∀ l, N → Matrix (BN l) (BN l) ℂ) (hRN : IsIrrepSystem RN)
    (O : Set ΛN)
    (Tσ : ΛN → Set G) (hTσ : ∀ σ ∈ O, IsLabelTransversal N BN RN Tσ σ)
    (Rext : ∀ l, inertia N RN l → Matrix (BN l) (BN l) ℂ)
    (hext : ∀ l, IsExtension N RN l (Rext l))
    {Λη : ΛN → Type} {Bη : ∀ σ, Λη σ → Type} [∀ σ η, Fintype (Bη σ η)]
    [∀ σ η, DecidableEq (Bη σ η)]
    (Rη : ∀ σ η, (inertia N RN σ ⧸ N.subgroupOf (inertia N RN σ)) →
      Matrix (Bη σ η) (Bη σ η) ℂ)
    (hRη : ∀ σ ∈ O, IsIrrepSystem (Rη σ))
    {σ : ΛN} (hσO : σ ∈ O) (η : Λη σ) (n : N) (tL : Tσ σ)
    (i_σ : BN σ) (j_η : Bη σ η) (o_mid : LBas BN Tσ Bη σ η) :
    littleRep N BN RN Tσ Rext Bη Rη σ η (n : G) (tL, (i_σ, j_η)) o_mid =
      if o_mid.1 = tL ∧ o_mid.2.2 = j_η then
        RN σ ⟨(tL : G)⁻¹ * (n : G) * (tL : G), conj_inv_mem N (tL : G) n⟩ i_σ o_mid.2.1
      else 0 := by
  rcases o_mid with ⟨t', i', j'⟩
  simp only [littleRep, indRep, inflation, Matrix.of_apply]
  let m : N := ⟨(tL : G)⁻¹ * (n : G) * (tL : G), conj_inv_mem N (tL : G) n⟩
  have hm_I : (m : G) ∈ inertia N RN σ :=
    mem_inertia_of_mem_normal N RN σ (hRN.1 σ).1 m
  have hmem_iff : (tL : G)⁻¹ * (n : G) * (t' : G) ∈ inertia N RN σ ↔ t' = tL := by
    have heq : (tL : G)⁻¹ * (n : G) * (t' : G) = (m : G) * ((tL : G)⁻¹ * (t' : G)) := by
      simp [m, mul_assoc]
    rw [heq, (inertia N RN σ).mul_mem_cancel_left hm_I]
    constructor
    · intro ht'
      exact (eq_of_inv_mul_mem_inertia N RN Tσ σ (hTσ σ hσO) ht').symm
    · rintro rfl
      simp [(inertia N RN σ).one_mem]
  by_cases ht : t' = tL
  · subst ht
    have hm' : (t' : G)⁻¹ * (n : G) * (t' : G) ∈ inertia N RN σ := hmem_iff.mpr rfl
    rw [dif_pos hm']
    let x : N.subgroupOf (inertia N RN σ) := ⟨⟨(t' : G)⁻¹ * (n : G) * (t' : G), hm'⟩, m.2⟩
    have hRext_eq : Rext σ ⟨(t' : G)⁻¹ * (n : G) * (t' : G), hm'⟩ = RN σ m := by
      simpa [x, inNInertia, inertiaToN, m] using (hext σ).2 x
    have hq_one : QuotientGroup.mk (⟨(t' : G)⁻¹ * (n : G) * (t' : G), hm'⟩ : inertia N RN σ) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr x.2
    rw [hRext_eq, hq_one, ((hRη σ hσO).1 η).1.1, Matrix.kronecker, Matrix.kronecker_apply]
    by_cases hj : j' = j_η
    · subst hj; simp [m]
    · have hj' : j_η ≠ j' := Ne.symm hj
      simp [hj, hj']
  · have hm_neg : ¬ (tL : G)⁻¹ * (n : G) * (t' : G) ∈ inertia N RN σ := fun h => ht (hmem_iff.mp h)
    rw [dif_neg hm_neg]
    simp [ht]

end GL2QFT.Supplement.Thm721Helpers

open GL2QFT.Supplement.Thm721Helpers

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
    (TN : Set G) (hTN : Subgroup.IsComplement (N : Set G) TN) :
    alg2 N BN RN O Tσ U Rext Bη Rη TN =
      fourierMatrix (fun p : GLab O (Λη := Λη) =>
        littleRep N BN RN Tσ Rext Bη Rη p.1.1 p.2) := by
  let _ := hO
  ext o g
  rcases o with ⟨⟨⟨σ, hσO⟩, η⟩, ⟨⟨tL, i_σ, j_η⟩, oR⟩⟩
  obtain ⟨⟨n₀, h₀⟩, hmul₀, _⟩ := hTN.existsUnique g
  have hg : ∃ h : TN, g * (h : G)⁻¹ ∈ N := by
    refine ⟨h₀, ?_⟩
    have heq : g * (h₀ : G)⁻¹ = (n₀ : G) := by
      calc g * (h₀ : G)⁻¹ = ((n₀ : G) * (h₀ : G)) * (h₀ : G)⁻¹ := by rw [← hmul₀]
        _ = (n₀ : G) := by simp
    rw [heq]
    exact n₀.2
  let h : TN := Classical.choose hg
  have hn_mem : g * (h : G)⁻¹ ∈ N := Classical.choose_spec hg
  let n : N := ⟨g * (h : G)⁻¹, hn_mem⟩
  have hnh : (n : G) * (h : G) = g := by
    simp [n, mul_assoc]
  have htr_mat : IsMatRep (transport N (RN σ) (tL : G)) :=
    transport_isMatRep N (hRN.1 σ).1 (tL : G)
  have htr_irr : IsIrreducibleRep (transport N (RN σ) (tL : G)) :=
    transport_isIrreducibleRep N (hRN.2.1 σ) (tL : G)
  obtain ⟨l, hl_equiv⟩ := hRN.2.2.2 (BN σ) (transport N (RN σ) (tL : G)) htr_mat htr_irr
  have hl_enc : IsOrbEnc N BN RN O Tσ l σ (tL : G) := ⟨hσO, tL.2, hl_equiv⟩
  have hl_uniq : ∀ l' : ΛN, IsOrbEnc N BN RN O Tσ l' σ (tL : G) → l' = l := by
    intro l' hl'
    by_contra hne
    have heq_ll' : RepEquiv (RN l') (RN l) :=
      repEquiv_trans hl'.2.2 (repEquiv_symm hl_equiv)
    exact hRN.2.2.1 l' l hne heq_ll'
  simp only [alg2, fourierMatrix, Matrix.of_apply]
  rw [dif_pos hg]
  have hsum_l :
      ∑ l' : ΛN,
          (if IsOrbEnc N BN RN O Tσ l' σ (tL : G) then
            ∑ i' : BN l', ∑ k' : BN l',
              (Real.sqrt ((Fintype.card (BN l') : ℝ) / (Fintype.card N : ℝ)) : ℂ) *
                RN l' n i' k' *
                conj (U σ (tL : G) l' i' i_σ) *
                stepsRight N BN RN Tσ U Rext Bη Rη TN l' σ tL ⟨η, j_η, oR⟩ (k', h)
          else 0) =
        ∑ i' : BN l, ∑ k' : BN l,
          (Real.sqrt ((Fintype.card (BN l) : ℝ) / (Fintype.card N : ℝ)) : ℂ) *
            RN l n i' k' *
            conj (U σ (tL : G) l i' i_σ) *
            stepsRight N BN RN Tσ U Rext Bη Rη TN l σ tL ⟨η, j_η, oR⟩ (k', h) := by
    refine (Finset.sum_eq_single l ?_ fun hmem => absurd (Finset.mem_univ _) hmem).trans ?_
    · intro l' _ hne
      rw [if_neg (fun hc => hne (hl_uniq l' hc))]
    · rw [if_pos hl_enc]
  rw [hsum_l]
  have h720 := stepsRight_eq_uIndRight N BN RN hRN O Tσ hTσ U hU Rext Bη Rη TN hTN l σ tL hl_enc
  rw [h720]
  simp only [uIndRight, Matrix.of_apply]
  have hcard_NTN : Fintype.card N * Fintype.card TN = Fintype.card G := by
    have hc := hTN.card_mul_card
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at hc
    exact hc
  have hBNl_pos : (0 : ℝ) < Fintype.card (BN l) :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr (hRN.2.1 l).1)
  have hN_pos : (0 : ℝ) < Fintype.card N :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨1⟩)
  have hTN_pos : (0 : ℝ) < Fintype.card TN :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨h⟩)
  have hsqrt_eq :
      (Real.sqrt ((Fintype.card (BN l) : ℝ) / (Fintype.card N : ℝ)) : ℂ) *
        (Real.sqrt ((Fintype.card (LBas BN Tσ Bη σ η) : ℝ) /
          ((Fintype.card (BN l) : ℝ) * (Fintype.card TN : ℝ))) : ℂ) =
        (Real.sqrt ((Fintype.card (LBas BN Tσ Bη σ η) : ℝ) / (Fintype.card G : ℝ)) : ℂ) := by
    rw [← Complex.ofReal_mul, ← Real.sqrt_mul (by positivity)]
    congr 2
    have hG_R : (Fintype.card G : ℝ) = (Fintype.card N : ℝ) * (Fintype.card TN : ℝ) := by
      exact_mod_cast hcard_NTN.symm
    rw [hG_R]
    field_simp
  have hsum_rearrange :
      ∑ i' : BN l, ∑ k' : BN l,
          (Real.sqrt ((Fintype.card (BN l) : ℝ) / (Fintype.card N : ℝ)) : ℂ) *
            RN l n i' k' *
            conj (U σ (tL : G) l i' i_σ) *
            ((Real.sqrt ((Fintype.card (LBas BN Tσ Bη σ η) : ℝ) /
              ((Fintype.card (BN l) : ℝ) * (Fintype.card TN : ℝ))) : ℂ) *
              ∑ i : BN σ, U σ (tL : G) l k' i *
                littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) (tL, (i, j_η)) oR) =
        (Real.sqrt ((Fintype.card (LBas BN Tσ Bη σ η) : ℝ) / (Fintype.card G : ℝ)) : ℂ) *
          ∑ i : BN σ,
            ((U σ (tL : G) l)ᴴ * RN l n * U σ (tL : G) l) i_σ i *
              littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) (tL, (i, j_η)) oR := by
    have h1 :
        ∑ i' : BN l, ∑ k' : BN l,
            (Real.sqrt ((Fintype.card (BN l) : ℝ) / (Fintype.card N : ℝ)) : ℂ) *
              RN l n i' k' *
              conj (U σ (tL : G) l i' i_σ) *
              ((Real.sqrt ((Fintype.card (LBas BN Tσ Bη σ η) : ℝ) /
                ((Fintype.card (BN l) : ℝ) * (Fintype.card TN : ℝ))) : ℂ) *
                ∑ i : BN σ, U σ (tL : G) l k' i *
                  littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) (tL, (i, j_η)) oR) =
          ((Real.sqrt ((Fintype.card (BN l) : ℝ) / (Fintype.card N : ℝ)) : ℂ) *
            (Real.sqrt ((Fintype.card (LBas BN Tσ Bη σ η) : ℝ) /
              ((Fintype.card (BN l) : ℝ) * (Fintype.card TN : ℝ))) : ℂ)) *
            ∑ i' : BN l, ∑ k' : BN l, ∑ i : BN σ,
              (conj (U σ (tL : G) l i' i_σ) * RN l n i' k' * U σ (tL : G) l k' i) *
                littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) (tL, (i, j_η)) oR := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i' _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k' _ => ?_
      simp_rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    rw [h1, hsqrt_eq]
    congr 1
    calc ∑ i' : BN l, ∑ k' : BN l, ∑ i : BN σ,
            (conj (U σ (tL : G) l i' i_σ) * RN l n i' k' * U σ (tL : G) l k' i) *
              littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) (tL, (i, j_η)) oR
        = ∑ i' : BN l, ∑ i : BN σ, ∑ k' : BN l,
            (conj (U σ (tL : G) l i' i_σ) * RN l n i' k' * U σ (tL : G) l k' i) *
              littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) (tL, (i, j_η)) oR := by
          refine Finset.sum_congr rfl fun i' _ => Finset.sum_comm
      _ = ∑ i : BN σ, ∑ i' : BN l, ∑ k' : BN l,
            (conj (U σ (tL : G) l i' i_σ) * RN l n i' k' * U σ (tL : G) l k' i) *
              littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) (tL, (i, j_η)) oR := Finset.sum_comm
      _ = ∑ i : BN σ,
            ((∑ k' : BN l, (∑ i' : BN l, conj (U σ (tL : G) l i' i_σ) * RN l n i' k') *
              U σ (tL : G) l k' i) *
              littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) (tL, (i, j_η)) oR) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm, Finset.sum_mul]
          refine Finset.sum_congr rfl fun k' _ => ?_
          rw [Finset.sum_mul, Finset.sum_mul]
      _ = ∑ i : BN σ,
            ((U σ (tL : G) l)ᴴ * RN l n * U σ (tL : G) l) i_σ i *
              littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) (tL, (i, j_η)) oR := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Complex.star_def]
  rw [hsum_rearrange]
  have hU_unit := hU.2 l σ (tL : G) hl_enc
  have hU_conj : (U σ (tL : G) l)ᴴ * RN l n * U σ (tL : G) l =
      transport N (RN σ) (tL : G) n := by
    calc (U σ (tL : G) l)ᴴ * RN l n * U σ (tL : G) l
        = (U σ (tL : G) l)ᴴ *
            (U σ (tL : G) l * transport N (RN σ) (tL : G) n * (U σ (tL : G) l)ᴴ) *
            U σ (tL : G) l := by rw [hU_unit.2.2 n]
      _ = ((U σ (tL : G) l)ᴴ * U σ (tL : G) l) * transport N (RN σ) (tL : G) n *
            ((U σ (tL : G) l)ᴴ * U σ (tL : G) l) := by simp only [Matrix.mul_assoc]
      _ = transport N (RN σ) (tL : G) n := by rw [hU_unit.2.1, Matrix.one_mul, Matrix.mul_one]
  rw [hU_conj]
  congr 1
  symm
  calc littleRep N BN RN Tσ Rext Bη Rη σ η g (tL, (i_σ, j_η)) oR
      = littleRep N BN RN Tσ Rext Bη Rη σ η ((n : G) * (h : G)) (tL, (i_σ, j_η)) oR := by
        rw [hnh]
    _ = (littleRep N BN RN Tσ Rext Bη Rη σ η (n : G) *
          littleRep N BN RN Tσ Rext Bη Rη σ η (h : G)) (tL, (i_σ, j_η)) oR := by
        rw [littleRep_mul N RN O Tσ hTσ Rext hext Rη hRη hσO η (n : G) (h : G)]
    _ = ∑ o_mid : LBas BN Tσ Bη σ η,
          littleRep N BN RN Tσ Rext Bη Rη σ η (n : G) (tL, (i_σ, j_η)) o_mid *
            littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) o_mid oR := by rw [Matrix.mul_apply]
    _ = ∑ t' : Tσ σ, ∑ ij : BN σ × Bη σ η,
          littleRep N BN RN Tσ Rext Bη Rη σ η (n : G) (tL, (i_σ, j_η)) (t', ij) *
            littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) (t', ij) oR := by
        rw [Fintype.sum_prod_type]
    _ = ∑ ij : BN σ × Bη σ η,
          littleRep N BN RN Tσ Rext Bη Rη σ η (n : G) (tL, (i_σ, j_η)) (tL, ij) *
            littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) (tL, ij) oR := by
        refine Finset.sum_eq_single tL ?_ fun hmem => absurd (Finset.mem_univ _) hmem
        intro t' _ hne
        refine Finset.sum_eq_zero fun ij _ => ?_
        rw [littleRep_mem_normal N RN hRN O Tσ hTσ Rext hext Rη hRη hσO η n tL i_σ j_η (t', ij)]
        simp [hne]
    _ = ∑ i : BN σ, ∑ j' : Bη σ η,
          littleRep N BN RN Tσ Rext Bη Rη σ η (n : G) (tL, (i_σ, j_η)) (tL, (i, j')) *
            littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) (tL, (i, j')) oR := by
        rw [Fintype.sum_prod_type]
    _ = ∑ i : BN σ,
          littleRep N BN RN Tσ Rext Bη Rη σ η (n : G) (tL, (i_σ, j_η)) (tL, (i, j_η)) *
            littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) (tL, (i, j_η)) oR := by
        refine Finset.sum_congr rfl fun i _ => ?_
        refine Finset.sum_eq_single j_η ?_ fun hmem => absurd (Finset.mem_univ _) hmem
        intro j' _ hne
        rw [littleRep_mem_normal N RN hRN O Tσ hTσ Rext hext Rη hRη hσO η n tL i_σ j_η
          (tL, (i, j'))]
        simp [hne]
    _ = ∑ i : BN σ,
          transport N (RN σ) (tL : G) n i_σ i *
            littleRep N BN RN Tσ Rext Bη Rη σ η (h : G) (tL, (i, j_η)) oR := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [littleRep_mem_normal N RN hRN O Tσ hTσ Rext hext Rη hRη hσO η n tL i_σ j_η
          (tL, (i, j_η))]
        simp [transport]
