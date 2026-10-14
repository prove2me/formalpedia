-- Prove2me | solution 1 for DRConvexOpt.InfConv.theorem_3
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-12T13:06:58.220252+00:00
-- url     : https://prove2.me/submissions/cc032aae-c905-4c94-91f3-cd23ac2e959d

import Mathlib
import Definitions.Def_DRConvexOpt_InfConv_Setting

open MeasureTheory Matrix Filter Topology

namespace RRAux_DRInfConv

open DRConvexOpt.InfConv

lemma ecoe_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    ((∑ i ∈ s, f i : ℝ) : EReal) = ∑ i ∈ s, ((f i : ℝ) : EReal) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, EReal.coe_add, ih]

lemma term_eq {nN nP nL : ℕ} (v : PWAff nN nP nL) (x : Fin nN → ℝ) (z : Fin nP → ℝ) (l : Fin nL) :
    (v.S l *ᵥ z + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ z + v.t0 l)
      = (x ᵥ* v.S l + v.tv l) ⬝ᵥ z + (v.s l ⬝ᵥ x + v.t0 l) := by
  rw [dotProduct_comm (v.S l *ᵥ z + v.s l) x, dotProduct_add, dotProduct_mulVec, add_dotProduct,
    dotProduct_comm x (v.s l)]
  ring

lemma int_lin {nP nQ : ℕ} (μ : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ))) [IsFiniteMeasure μ]
    (h : Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => ω) μ) (a : Fin nP → ℝ) (c : ℝ) :
    Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => a ⬝ᵥ ω.1 + c) μ := by
  have hc : ∀ i, Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => ω.1 i) μ := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin nP => ℝ) i).integrable_comp h.fst
  simp only [dotProduct]
  exact (integrable_finsetSum _ fun i _ => (hc i).const_mul (a i)).add (integrable_const c)

lemma int_sup {α : Type*} [MeasurableSpace α] (μ : Measure α) {nL : ℕ} [NeZero nL]
    (F : Fin nL → α → ℝ) (hF : ∀ l, Integrable (F l) μ) :
    Integrable (fun ω => Finset.univ.sup' Finset.univ_nonempty (fun l => F l ω)) μ := by
  have : (fun ω => Finset.univ.sup' Finset.univ_nonempty (fun l => F l ω))
      = Finset.univ.sup' Finset.univ_nonempty F := by
    funext ω; rw [Finset.sup'_apply]
  rw [this]
  exact Finset.sup'_induction _ _ (p := fun g => Integrable g μ) (fun a ha b hb => ha.sup hb)
    (fun l _ => hF l)

lemma int_eval {nP nQ nN nL : ℕ} [NeZero nL] (v : PWAff nN nP nL)
    (μ : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ))) [IsFiniteMeasure μ]
    (h : Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => ω) μ) (x : Fin nN → ℝ) :
    Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => v.eval x ω.1) μ := by
  unfold PWAff.eval
  simp only [term_eq]
  exact int_sup μ _ (fun l => int_lin μ h _ _)

noncomputable def Gf {nN nP nL : ℕ} (v : PWAff nN nP nL) (z : Fin nP → ℝ) : ℝ :=
  ∑ l, |v.tv l ⬝ᵥ z + v.t0 l|

lemma conv_pt {nN nP nL nJ : ℕ} [NeZero nL] (v : PWAff nN nP nL) (y : Fin nJ → Fin nN → ℝ)
    (δ : Fin nJ → ℝ) (hδ : ∀ j, 0 < δ j) (hsum : ∑ j, δ j = 1) (z : Fin nP → ℝ) :
    v.eval (∑ j, y j) z ≤ ∑ j, δ j * v.eval ((δ j)⁻¹ • y j) z := by
  conv_lhs => unfold PWAff.eval
  apply Finset.sup'_le
  intro l _
  have key : (v.S l *ᵥ z + v.s l) ⬝ᵥ (∑ j, y j) + (v.tv l ⬝ᵥ z + v.t0 l)
      = ∑ j, δ j * ((v.S l *ᵥ z + v.s l) ⬝ᵥ ((δ j)⁻¹ • y j) + (v.tv l ⬝ᵥ z + v.t0 l)) := by
    rw [dotProduct_sum]
    simp_rw [dotProduct_smul, smul_eq_mul]
    have : ∀ j, δ j * ((δ j)⁻¹ * ((v.S l *ᵥ z + v.s l) ⬝ᵥ y j) + (v.tv l ⬝ᵥ z + v.t0 l))
        = (v.S l *ᵥ z + v.s l) ⬝ᵥ y j + δ j * (v.tv l ⬝ᵥ z + v.t0 l) := by
      intro j; have := (hδ j).ne'; field_simp
    simp_rw [this]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [key]
  refine Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left ?_ (hδ j).le)
  unfold PWAff.eval
  exact Finset.le_sup' (fun l => (v.S l *ᵥ z + v.s l) ⬝ᵥ ((δ j)⁻¹ • y j) + (v.tv l ⬝ᵥ z + v.t0 l))
    (Finset.mem_univ l)

lemma persp_pt {nN nP nL : ℕ} [NeZero nL] (v : PWAff nN nP nL) (x : Fin nN → ℝ) (δ : ℝ)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (z : Fin nP → ℝ) :
    δ * v.eval (δ⁻¹ • x) z ≤ v.eval x z + (1 - δ) * Gf v z := by
  rw [← le_div_iff₀' hδ0]
  unfold PWAff.eval
  apply Finset.sup'_le
  intro l _
  rw [le_div_iff₀' hδ0, dotProduct_smul, smul_eq_mul]
  have h1 := Finset.le_sup' (fun l => (v.S l *ᵥ z + v.s l) ⬝ᵥ x + (v.tv l ⬝ᵥ z + v.t0 l))
    (Finset.mem_univ l)
  have h2 : |v.tv l ⬝ᵥ z + v.t0 l| ≤ Gf v z :=
    Finset.single_le_sum (f := fun l => |v.tv l ⬝ᵥ z + v.t0 l|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ l)
  have h3 := neg_abs_le (v.tv l ⬝ᵥ z + v.t0 l)
  have e : δ * (δ⁻¹ * ((v.S l *ᵥ z + v.s l) ⬝ᵥ x) + (v.tv l ⬝ᵥ z + v.t0 l))
      = (v.S l *ᵥ z + v.s l) ⬝ᵥ x + δ * (v.tv l ⬝ᵥ z + v.t0 l) := by
    field_simp
  rw [e]
  linarith [mul_le_mul_of_nonneg_left h2 (by linarith : (0:ℝ) ≤ 1 - δ),
    mul_le_mul_of_nonneg_left h3 (by linarith : (0:ℝ) ≤ 1 - δ)]

lemma zero_pt {nN nP nL : ℕ} [NeZero nL] (v : PWAff nN nP nL) (z : Fin nP → ℝ) :
    v.eval 0 z ≤ Gf v z := by
  unfold PWAff.eval
  apply Finset.sup'_le
  intro l _
  rw [dotProduct_zero, zero_add]
  exact (le_abs_self _).trans (Finset.single_le_sum (f := fun l => |v.tv l ⬝ᵥ z + v.t0 l|)
    (fun _ _ => abs_nonneg _) (Finset.mem_univ l))

lemma G_bound {nN nP nL : ℕ} (v : PWAff nN nP nL) (z : Fin nP → ℝ) :
    Gf v z ≤ (∑ l, ∑ i, |v.tv l i|) * ‖z‖ + ∑ l, |v.t0 l| := by
  unfold Gf
  rw [Finset.sum_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun l _ => ?_)
  refine (abs_add_le _ _).trans (add_le_add_left ?_ _)
  rw [Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun i _ => ?_))
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs (z i)).symm ▸ norm_le_pi_norm z i)
    (abs_nonneg _)

lemma G_int {nP nQ nN nL : ℕ} (v : PWAff nN nP nL)
    (μ : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ))) [IsFiniteMeasure μ]
    (h : Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => ω) μ) :
    Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => Gf v ω.1) μ := by
  unfold Gf
  exact integrable_finsetSum _ (fun l _ => (int_lin μ h _ _).abs)

lemma G_integral {nP nQ nN nL : ℕ} (v : PWAff nN nP nL)
    (μ : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ))) [IsProbabilityMeasure μ]
    (h : Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => ω) μ) :
    ∫ ω, Gf v ω.1 ∂μ ≤ (∑ l, ∑ i, |v.tv l i|) * ∫ ω, ‖ω.1‖ ∂μ + ∑ l, |v.t0 l| := by
  have hn : Integrable (fun ω : (Fin nP → ℝ) × (Fin nQ → ℝ) => ‖ω.1‖) μ := h.fst.norm
  calc ∫ ω, Gf v ω.1 ∂μ ≤ ∫ ω, ((∑ l, ∑ i, |v.tv l i|) * ‖ω.1‖ + ∑ l, |v.t0 l|) ∂μ :=
        integral_mono (G_int v μ h) ((hn.const_mul _).add (integrable_const _))
          (fun ω => G_bound v ω.1)
    _ = _ := by
        rw [integral_add (hn.const_mul _) (integrable_const _), integral_const_mul, integral_const,
          probReal_univ, one_smul]

lemma wc_le {Ω : Type*} [MeasurableSpace Ω] (P : Set (Measure Ω)) (φ : Ω → ℝ) (δ b : ℝ)
    (hδ : 0 < δ) (h : ∀ μ ∈ P, δ * ∫ ω, φ ω ∂μ ≤ b) :
    ((δ : ℝ) : EReal) * worstCase P φ ≤ (b : EReal) := by
  have hW : worstCase P φ ≤ ((b / δ : ℝ) : EReal) :=
    iSup₂_le fun μ hμ => EReal.coe_le_coe_iff.2 (by rw [le_div_iff₀' hδ]; exact h μ hμ)
  calc ((δ : ℝ) : EReal) * worstCase P φ ≤ ((δ : ℝ) : EReal) * ((b / δ : ℝ) : EReal) :=
        mul_le_mul_of_nonneg_left hW (EReal.coe_nonneg.2 hδ.le)
    _ = (b : EReal) := by
        rw [← EReal.coe_mul]; congr 1; field_simp

lemma le_wc {Ω : Type*} [MeasurableSpace Ω] (P : Set (Measure Ω)) (φ : Ω → ℝ) (δ : ℝ)
    (hδ : 0 ≤ δ) (μ : Measure Ω) (hμ : μ ∈ P) :
    ((δ * ∫ ω, φ ω ∂μ : ℝ) : EReal) ≤ ((δ : ℝ) : EReal) * worstCase P φ := by
  rw [EReal.coe_mul]
  exact mul_le_mul_of_nonneg_left
    (le_iSup₂ (f := fun μ (_ : μ ∈ P) => ((∫ ω, φ ω ∂μ : ℝ) : EReal)) μ hμ)
    (EReal.coe_nonneg.2 hδ)

lemma eps_facts (J R η : ℝ) (hJ : 1 ≤ J) (hR : 0 ≤ R) (hη : 0 < η) :
    ∃ ε : ℝ, 0 < ε ∧ J * ε ≤ 1 / 2 ∧ ε * ((J + 1) * R) ≤ η := by
  have hJ0 : 0 < J := by linarith
  have hD : 0 < (J + 1) * (R + 1) := by positivity
  refine ⟨min (1 / (2 * J)) (η / ((J + 1) * (R + 1))), lt_min (by positivity) (by positivity), ?_, ?_⟩
  · calc J * min (1 / (2 * J)) (η / ((J + 1) * (R + 1))) ≤ J * (1 / (2 * J)) :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) hJ0.le
      _ = 1 / 2 := by field_simp
  · have hε0 : 0 ≤ min (1 / (2 * J)) (η / ((J + 1) * (R + 1))) :=
      le_min (by positivity) (by positivity)
    calc min (1 / (2 * J)) (η / ((J + 1) * (R + 1))) * ((J + 1) * R)
        ≤ min (1 / (2 * J)) (η / ((J + 1) * (R + 1))) * ((J + 1) * (R + 1)) :=
          mul_le_mul_of_nonneg_left (by nlinarith) hε0
      _ ≤ η / ((J + 1) * (R + 1)) * ((J + 1) * (R + 1)) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hD.le
      _ = η := by field_simp

lemma sum_arith (w ε J R Bj0 η : ℝ) (hJ : 1 ≤ J) (hε : 0 < ε) (hB : 0 ≤ Bj0) (hBR : Bj0 ≤ R)
    (hη : ε * ((J + 1) * R) ≤ η) :
    w + (J - 1) * ε * Bj0 + ε * R ≤ w + η := by
  have h1 : (J - 1) * ε * Bj0 ≤ (J - 1) * ε * R :=
    mul_le_mul_of_nonneg_left hBR (mul_nonneg (by linarith) hε.le)
  nlinarith

lemma part2 {nP nQ nK nI nN nL nJ : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL) (blk : Fin (nI + 1) → Fin nJ)
    (x : Fin nN → ℝ) (μ : Measure ((Fin nP → ℝ) × (Fin nQ → ℝ))) (hμ : μ ∈ ambiguitySet d) :
    ((∫ ω, v.eval x ω.1 ∂μ : ℝ) : EReal) ≤ infConvBound d blk v x := by
  obtain ⟨hP, hint, hb, hconf⟩ := hμ
  have hmem : ∀ j, μ ∈ outerSet d blk j := fun j => ⟨hP, hint, hb, fun i _ => hconf i⟩
  unfold infConvBound
  refine le_iInf₂ (fun p hp => ?_)
  obtain ⟨hy, hδs, hδ⟩ := hp
  calc ((∫ ω, v.eval x ω.1 ∂μ : ℝ) : EReal)
      ≤ ((∫ ω, ∑ j, p.2 j * v.eval ((p.2 j)⁻¹ • p.1 j) ω.1 ∂μ : ℝ) : EReal) := by
        refine EReal.coe_le_coe_iff.2 (integral_mono (int_eval v μ hint x)
          (integrable_finsetSum _ (fun j _ => (int_eval v μ hint _).const_mul _)) (fun ω => ?_))
        have := conv_pt v p.1 p.2 hδ hδs ω.1
        rwa [hy] at this
    _ = ((∑ j, p.2 j * ∫ ω, v.eval ((p.2 j)⁻¹ • p.1 j) ω.1 ∂μ : ℝ) : EReal) := by
        rw [integral_finsetSum _ (fun j _ => (int_eval v μ hint _).const_mul _)]
        simp_rw [integral_const_mul]
    _ = ∑ j, ((p.2 j * ∫ ω, v.eval ((p.2 j)⁻¹ • p.1 j) ω.1 ∂μ : ℝ) : EReal) := ecoe_sum _ _
    _ ≤ _ := Finset.sum_le_sum (fun j _ => le_wc _ _ _ (hδ j).le μ (hmem j))

lemma part3 {nP nQ nK nI nN nL : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL) (blk : Fin (nI + 1) → Fin 1)
    (x : Fin nN → ℝ) (w : ℝ) (h3 : ∀ μ ∈ ambiguitySet d, ∫ ω, v.eval x ω.1 ∂μ ≤ w) :
    infConvBound d blk v x ≤ (w : EReal) ∧ naiveBound d blk v x ≤ (w : EReal) := by
  have hout : ∀ j, outerSet d blk j = ambiguitySet d := by
    intro j; ext μ
    simp only [outerSet, ambiguitySet, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨a, b, c, e⟩; exact ⟨a, b, c, fun i => e i (Subsingleton.elim _ _)⟩
    · rintro ⟨a, b, c, e⟩; exact ⟨a, b, c, fun i _ => e i⟩
  have hW : ∀ j, worstCase (outerSet d blk j) (fun ω => v.eval x ω.1) ≤ (w : EReal) := by
    intro j; rw [hout]
    exact iSup₂_le fun μ hμ => EReal.coe_le_coe_iff.2 (h3 μ hμ)
  constructor
  · unfold infConvBound
    refine (iInf₂_le ((fun _ => x, fun _ => 1) : (Fin 1 → Fin nN → ℝ) × (Fin 1 → ℝ))
      ⟨by simp, by simp, fun _ => one_pos⟩).trans ?_
    simp only [Fin.sum_univ_one, inv_one, one_smul, EReal.coe_one, one_mul]
    exact hW 0
  · exact (iInf_le _ 0).trans (hW 0)

lemma part1 {nP nQ nK nI nN nL nJ : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL) (blk : Fin (nI + 1) → Fin nJ)
    (hFM : UnifFirstMoment d blk) (x : Fin nN → ℝ) (w : ℝ)
    (h6 : naiveBound d blk v x ≤ (w : EReal)) : infConvBound d blk v x ≤ (w : EReal) := by
  have hne : Nonempty (Fin nJ) := ⟨blk 0⟩
  obtain ⟨j0, hj0⟩ := exists_eq_ciInf_of_finite
    (f := fun j => worstCase (outerSet d blk j) (fun ω => v.eval x ω.1))
  have hx : ∀ μ ∈ outerSet d blk j0, ∫ ω, v.eval x ω.1 ∂μ ≤ w := by
    intro μ hμ
    have h1 : worstCase (outerSet d blk j0) (fun ω => v.eval x ω.1) ≤ (w : EReal) := by
      rw [hj0]; exact h6
    exact EReal.coe_le_coe_iff.1
      ((le_iSup₂ (f := fun μ (_ : μ ∈ outerSet d blk j0) =>
        ((∫ ω, v.eval x ω.1 ∂μ : ℝ) : EReal)) μ hμ).trans h1)
  choose M hM using hFM
  have hc1 : 0 ≤ ∑ l, ∑ i, |v.tv l i| :=
    Finset.sum_nonneg (fun l _ => Finset.sum_nonneg (fun i _ => abs_nonneg _))
  have hc0 : 0 ≤ ∑ l, |v.t0 l| := Finset.sum_nonneg (fun l _ => abs_nonneg _)
  let B : Fin nJ → ℝ := fun j => (∑ l, ∑ i, |v.tv l i|) * max (M j) 0 + ∑ l, |v.t0 l|
  have hB : ∀ j, ∀ μ ∈ outerSet d blk j, ∫ ω, Gf v ω.1 ∂μ ≤ B j := by
    intro j μ hμ
    have hμ' := hμ
    obtain ⟨hP, hint, _, _⟩ := hμ'
    exact (G_integral v μ hint).trans (add_le_add_left
      (mul_le_mul_of_nonneg_left ((hM j μ hμ).trans (le_max_left _ _)) hc1) _)
  have hB0 : ∀ j, 0 ≤ B j := fun j => add_nonneg (mul_nonneg hc1 (le_max_right _ _)) hc0
  have hBR : B j0 ≤ ∑ j, B j :=
    Finset.single_le_sum (f := B) (fun j _ => hB0 j) (Finset.mem_univ j0)
  have hJ : (1 : ℝ) ≤ (nJ : ℝ) := by
    have : 0 < nJ := Fin.pos j0
    exact_mod_cast this
  rw [← EReal.le_of_forall_lt_iff_le]
  intro z hz
  have hη : 0 < z - w := by have := EReal.coe_lt_coe_iff.1 hz; linarith
  obtain ⟨ε, hε0, hεJ, hεη⟩ :=
    eps_facts (nJ : ℝ) (∑ j, B j) (z - w) hJ (Finset.sum_nonneg (fun j _ => hB0 j)) hη
  let δ : Fin nJ → ℝ := fun j => ε + if j = j0 then 1 - (nJ : ℝ) * ε else 0
  let y : Fin nJ → Fin nN → ℝ := fun j => if j = j0 then x else 0
  have hδpos : ∀ j, 0 < δ j := by
    intro j; simp only [δ]; split_ifs <;> linarith
  have hδsum : ∑ j, δ j = 1 := by
    simp only [δ]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq']
    simp
  have hysum : ∑ j, y j = x := by simp [y]
  have hδj0 : δ j0 = 1 - ((nJ : ℝ) - 1) * ε := by simp [δ]; ring
  let bnd : Fin nJ → ℝ := fun j => if j = j0 then w + ((nJ : ℝ) - 1) * ε * B j0 else ε * B j
  have hterm : ∀ j, ((δ j : ℝ) : EReal) *
      worstCase (outerSet d blk j) (fun ω => v.eval ((δ j)⁻¹ • y j) ω.1) ≤ ((bnd j : ℝ) : EReal) := by
    intro j
    apply wc_le _ _ _ _ (hδpos j)
    intro μ hμ
    have hμ' := hμ
    obtain ⟨hP, hint, _, _⟩ := hμ
    by_cases hj : j = j0
    · subst hj
      have hyj : y j = x := if_pos rfl
      have hδ1 : δ j ≤ 1 := by rw [hδj0]; nlinarith
      rw [hyj]
      calc δ j * ∫ ω, v.eval ((δ j)⁻¹ • x) ω.1 ∂μ
          = ∫ ω, δ j * v.eval ((δ j)⁻¹ • x) ω.1 ∂μ := (integral_const_mul _ _).symm
        _ ≤ ∫ ω, (v.eval x ω.1 + (1 - δ j) * Gf v ω.1) ∂μ :=
            integral_mono ((int_eval v μ hint _).const_mul _)
              ((int_eval v μ hint _).add ((G_int v μ hint).const_mul _))
              (fun ω => persp_pt v x (δ j) (hδpos j) hδ1 ω.1)
        _ = ∫ ω, v.eval x ω.1 ∂μ + (1 - δ j) * ∫ ω, Gf v ω.1 ∂μ := by
            rw [integral_add (int_eval v μ hint _) ((G_int v μ hint).const_mul _),
              integral_const_mul]
        _ ≤ w + (1 - δ j) * B j :=
            add_le_add (hx μ hμ') (mul_le_mul_of_nonneg_left (hB j μ hμ') (by linarith))
        _ = bnd j := by
            simp only [bnd, if_pos rfl]; rw [hδj0]; ring
    · have hyj : y j = 0 := if_neg hj
      have hδj : δ j = ε := by simp only [δ, if_neg hj, add_zero]
      calc δ j * ∫ ω, v.eval ((δ j)⁻¹ • y j) ω.1 ∂μ = ε * ∫ ω, v.eval 0 ω.1 ∂μ := by
            rw [hyj, smul_zero, hδj]
        _ ≤ ε * ∫ ω, Gf v ω.1 ∂μ :=
            mul_le_mul_of_nonneg_left (integral_mono (int_eval v μ hint _) (G_int v μ hint)
              (fun ω => zero_pt v ω.1)) hε0.le
        _ ≤ ε * B j := mul_le_mul_of_nonneg_left (hB j μ hμ') hε0.le
        _ = bnd j := by simp only [bnd, if_neg hj]
  have hsum : ∑ j, bnd j ≤ z := by
    have h1 : ∀ j, bnd j ≤ (if j = j0 then w + ((nJ : ℝ) - 1) * ε * B j0 else 0) + ε * B j := by
      intro j
      simp only [bnd]
      have := mul_nonneg hε0.le (hB0 j)
      split_ifs <;> linarith
    calc ∑ j, bnd j ≤ ∑ j, ((if j = j0 then w + ((nJ : ℝ) - 1) * ε * B j0 else 0) + ε * B j) :=
          Finset.sum_le_sum (fun j _ => h1 j)
      _ = w + ((nJ : ℝ) - 1) * ε * B j0 + ε * ∑ j, B j := by
          rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mul_sum]
          simp
      _ ≤ w + (z - w) := sum_arith w ε _ _ _ _ hJ hε0 (hB0 j0) hBR hεη
      _ = z := by ring
  calc infConvBound d blk v x
      ≤ ∑ j, ((δ j : ℝ) : EReal) *
          worstCase (outerSet d blk j) (fun ω => v.eval ((δ j)⁻¹ • y j) ω.1) := by
        unfold infConvBound
        exact iInf₂_le ((y, δ) : (Fin nJ → Fin nN → ℝ) × (Fin nJ → ℝ)) ⟨hysum, hδsum, hδpos⟩
    _ ≤ ∑ j, ((bnd j : ℝ) : EReal) := Finset.sum_le_sum (fun j _ => hterm j)
    _ = ((∑ j, bnd j : ℝ) : EReal) := (ecoe_sum _ _).symm
    _ ≤ (z : EReal) := EReal.coe_le_coe_iff.2 hsum

end RRAux_DRInfConv

open DRConvexOpt.InfConv MeasureTheory Matrix Filter Topology in
theorem solution {nP nQ nK nI nN nL nJ : ℕ} [NeZero nL]
    (d : AmbData nP nQ nK nI) (v : PWAff nN nP nL)
    (blk : Fin (nI + 1) → Fin nJ) (hblk : Function.Surjective blk)
    (hK : ∀ i, IsProperCone (d.K i))
    (hp : ∀ i, 0 ≤ d.plo i ∧ d.plo i ≤ d.phi i ∧ d.phi i ≤ 1)
    (hC1 : Bornology.IsBounded (d.conf (Fin.last nI)) ∧ d.plo (Fin.last nI) = 1 ∧
      d.phi (Fin.last nI) = 1)
    (hC2 : ∃ μ ∈ ambiguitySet d, ∀ i, d.plo i < d.phi i →
      μ.real (d.conf i) ∈ Set.Ioo (d.plo i) (d.phi i))
    (hN' : WeakNesting d blk) (hFM : UnifFirstMoment d blk)
    (x : Fin nN → ℝ) (w : ℝ) :
    (naiveBound d blk v x ≤ (w : EReal) → infConvBound d blk v x ≤ (w : EReal)) ∧
    (infConvBound d blk v x ≤ (w : EReal) →
      ∀ μ ∈ ambiguitySet d, ∫ ω, v.eval x ω.1 ∂μ ≤ w) ∧
    (nJ = 1 → (∀ μ ∈ ambiguitySet d, ∫ ω, v.eval x ω.1 ∂μ ≤ w) →
      infConvBound d blk v x ≤ (w : EReal) ∧ naiveBound d blk v x ≤ (w : EReal)) := by
  refine ⟨RRAux_DRInfConv.part1 d v blk hFM x w, fun h μ hμ =>
    EReal.coe_le_coe_iff.1 ((RRAux_DRInfConv.part2 d v blk x μ hμ).trans h), ?_⟩
  intro hJ h3
  subst hJ
  exact RRAux_DRInfConv.part3 d v blk x w h3

#print axioms solution
