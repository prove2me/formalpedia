-- Prove2me | solution 1 for BauerleRiederMDP.MeanVariance.theorem_4_6_6
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-13T09:17:40.941403+00:00
-- url     : https://prove2.me/submissions/8c54f9ca-42fb-4cd0-a281-40df77601f08

import Mathlib
import Definitions.Def_MDPFinance_MeanVariance_MVMarket
import Definitions.Def_MDPFinance_MeanVariance_MVAuxiliary
import Definitions.Def_BauerleRiederMDP_MeanVariance_dcoef

set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MV466

open MDPFinance.MeanVariance BauerleRiederMDP.MeanVariance Matrix

section Quad

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

noncomputable def Ev (P : Measure Ω) (Rv : Ω → Fin d → ℝ) : Fin d → ℝ :=
  fun j => ∫ ω, Rv ω j ∂P

noncomputable def Cm (P : Measure Ω) (Rv : Ω → Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun j k => ∫ ω, Rv ω j * Rv ω k ∂P

variable {P : Measure Ω} [IsProbabilityMeasure P] {Rv : Ω → Fin d → ℝ}

lemma int_mul_L2 {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Integrable (fun ω => f ω * g ω) P := by
  have h := ((hf.add hg).integrable_sq.sub (hf.sub hg).integrable_sq).div_const 4
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only [Pi.add_apply, Pi.sub_apply]; ring

lemma lin_memLp (hL2 : ∀ k, MemLp (fun ω => Rv ω k) 2 P) (z : ℝ) (b : Fin d → ℝ) :
    MemLp (fun ω => z + ∑ j, b j * Rv ω j) 2 P :=
  (memLp_const z).add (memLp_finsetSum _ fun j _ => (hL2 j).const_mul (b j))

lemma lin_int (hL2 : ∀ k, MemLp (fun ω => Rv ω k) 2 P) (z : ℝ) (b : Fin d → ℝ) :
    ∫ ω, (z + ∑ j, b j * Rv ω j) ∂P = z + b ⬝ᵥ Ev P Rv := by
  have hI : ∀ j, Integrable (fun ω => Rv ω j) P := fun j => (hL2 j).integrable one_le_two
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun j _ => (hI j).const_mul (b j)),
    integral_finsetSum _ fun j _ => (hI j).const_mul (b j)]
  simp [integral_const_mul, dotProduct, Ev]

lemma quad (hL2 : ∀ k, MemLp (fun ω => Rv ω k) 2 P) (z : ℝ) (b : Fin d → ℝ) :
    ∫ ω, (z + ∑ j, b j * Rv ω j) ^ 2 ∂P
      = z ^ 2 + 2 * z * (b ⬝ᵥ Ev P Rv) + b ⬝ᵥ (Cm P Rv *ᵥ b) := by
  have hI : ∀ j, Integrable (fun ω => Rv ω j) P := fun j => (hL2 j).integrable one_le_two
  have hII : ∀ j k, Integrable (fun ω => Rv ω j * Rv ω k) P :=
    fun j k => int_mul_L2 (hL2 j) (hL2 k)
  have hA : Integrable (fun ω => ∑ j, b j * Rv ω j) P :=
    integrable_finsetSum _ fun j _ => (hI j).const_mul (b j)
  have hB : Integrable (fun ω => ∑ j, ∑ k, b j * b k * (Rv ω j * Rv ω k)) P :=
    integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => (hII j k).const_mul _
  have hpt : ∀ ω, (z + ∑ j, b j * Rv ω j) ^ 2
      = z ^ 2 + (2 * z * ∑ j, b j * Rv ω j + ∑ j, ∑ k, b j * b k * (Rv ω j * Rv ω k)) := by
    intro ω
    have : (∑ j, b j * Rv ω j) ^ 2 = ∑ j, ∑ k, b j * b k * (Rv ω j * Rv ω k) := by
      rw [sq, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
    rw [add_sq, this]; ring
  have e1 : ∫ ω, ∑ j, b j * Rv ω j ∂P = b ⬝ᵥ Ev P Rv := by
    rw [integral_finsetSum _ fun j _ => (hI j).const_mul (b j)]
    simp only [integral_const_mul, dotProduct, Ev]
  have e2 : ∫ ω, ∑ j, ∑ k, b j * b k * (Rv ω j * Rv ω k) ∂P = b ⬝ᵥ (Cm P Rv *ᵥ b) := by
    rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ => (hII j k).const_mul _]
    simp only [dotProduct, mulVec, Cm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [integral_finsetSum _ fun k _ => (hII j k).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul]; ring
  have hc : ∫ _ : Ω, z ^ 2 ∂P = z ^ 2 := by simp
  have hAB : Integrable (fun ω => 2 * z * ∑ j, b j * Rv ω j +
      ∑ j, ∑ k, b j * b k * (Rv ω j * Rv ω k)) P := (hA.const_mul (2 * z)).add hB
  simp_rw [hpt]
  rw [integral_add (integrable_const _) hAB,
    integral_add (hA.const_mul (2 * z)) hB, integral_const_mul, e1, e2, hc]
  ring

lemma Cm_transpose : (Cm P Rv)ᵀ = Cm P Rv := by
  ext j k
  simp only [transpose_apply, Cm]
  congr 1; funext ω; ring

lemma Cm_symm (v w : Fin d → ℝ) : v ⬝ᵥ (Cm P Rv *ᵥ w) = w ⬝ᵥ (Cm P Rv *ᵥ v) := by
  have h := vecMul_transpose (Cm P Rv) v
  rw [Cm_transpose] at h
  rw [dotProduct_mulVec, h, dotProduct_comm]

lemma Cm_psd (hL2 : ∀ k, MemLp (fun ω => Rv ω k) 2 P) (v : Fin d → ℝ) :
    0 ≤ v ⬝ᵥ (Cm P Rv *ᵥ v) := by
  have h := quad hL2 0 v
  rw [show (0 : ℝ) ^ 2 + 2 * 0 * (v ⬝ᵥ Ev P Rv) + v ⬝ᵥ (Cm P Rv *ᵥ v)
      = v ⬝ᵥ (Cm P Rv *ᵥ v) by ring] at h
  rw [← h]
  exact integral_nonneg fun ω => sq_nonneg _

lemma Cm_pd (hL2 : ∀ k, MemLp (fun ω => Rv ω k) 2 P)
    (hPD : (Matrix.of fun j k => ∫ ω, (Rv ω j - ∫ ω', Rv ω' j ∂P) *
      (Rv ω k - ∫ ω', Rv ω' k ∂P) ∂P).PosDef)
    (v : Fin d → ℝ) (hv : v ≠ 0) : 0 < v ⬝ᵥ (Cm P Rv *ᵥ v) := by
  have hL2' : ∀ k, MemLp (fun ω => Rv ω k - Ev P Rv k) 2 P :=
    fun k => (hL2 k).sub (memLp_const _)
  have h1 := hPD.dotProduct_mulVec_pos hv
  rw [star_trivial] at h1
  have e1 : (Matrix.of fun j k => ∫ ω, (Rv ω j - ∫ ω', Rv ω' j ∂P) *
      (Rv ω k - ∫ ω', Rv ω' k ∂P) ∂P) = Cm P (fun ω k => Rv ω k - Ev P Rv k) := rfl
  rw [e1] at h1
  have q1 := quad (Rv := fun ω k => Rv ω k - Ev P Rv k) hL2' 0 v
  have q2 := quad hL2 (-(v ⬝ᵥ Ev P Rv)) v
  have hpt : ∀ ω, (0 + ∑ j, v j * (Rv ω j - Ev P Rv j))
      = -(v ⬝ᵥ Ev P Rv) + ∑ j, v j * Rv ω j := by
    intro ω; simp only [mul_sub, Finset.sum_sub_distrib, dotProduct]; ring
  simp_rw [hpt] at q1
  rw [q2] at q1
  nlinarith [sq_nonneg (v ⬝ᵥ Ev P Rv)]

lemma G_moments (hL2 : ∀ k, MemLp (fun ω => Rv ω k) 2 P) {h : Fin d → ℝ}
    (hinv : Cm P Rv *ᵥ h = Ev P Rv) :
    ∫ ω, (1 + ∑ j, (-h) j * Rv ω j) ∂P = 1 - Ev P Rv ⬝ᵥ h ∧
    ∫ ω, (1 + ∑ j, (-h) j * Rv ω j) ^ 2 ∂P = 1 - Ev P Rv ⬝ᵥ h := by
  constructor
  · rw [lin_int hL2, neg_dotProduct, dotProduct_comm h]; ring
  · rw [quad hL2]
    simp only [mulVec_neg, hinv, neg_dotProduct, dotProduct_neg, neg_neg]
    rw [dotProduct_comm h]; ring

lemma quad_lower (hL2 : ∀ k, MemLp (fun ω => Rv ω k) 2 P) {h : Fin d → ℝ}
    (hinv : Cm P Rv *ᵥ h = Ev P Rv) (z : ℝ) (b : Fin d → ℝ) :
    (1 - Ev P Rv ⬝ᵥ h) * z ^ 2 ≤ z ^ 2 + 2 * z * (b ⬝ᵥ Ev P Rv) + b ⬝ᵥ (Cm P Rv *ᵥ b) := by
  have hv := Cm_psd hL2 (b + z • h)
  have hs : h ⬝ᵥ (Cm P Rv *ᵥ b) = b ⬝ᵥ Ev P Rv := by rw [Cm_symm, hinv]
  have e : (b + z • h) ⬝ᵥ (Cm P Rv *ᵥ (b + z • h))
      = b ⬝ᵥ (Cm P Rv *ᵥ b) + 2 * z * (b ⬝ᵥ Ev P Rv) + z ^ 2 * (Ev P Rv ⬝ᵥ h) := by
    simp only [mulVec_add, mulVec_smul, add_dotProduct, dotProduct_add, smul_dotProduct,
      dotProduct_smul, smul_eq_mul, hinv, hs]
    rw [dotProduct_comm h (Ev P Rv)]; ring
  rw [e] at hv
  nlinarith

lemma ell_facts (hL2 : ∀ k, MemLp (fun ω => Rv ω k) 2 P)
    (hPD : (Matrix.of fun j k => ∫ ω, (Rv ω j - ∫ ω', Rv ω' j ∂P) *
      (Rv ω k - ∫ ω', Rv ω' k ∂P) ∂P).PosDef)
    (hE : Ev P Rv ≠ 0) :
    Cm P Rv *ᵥ ((Cm P Rv)⁻¹ *ᵥ Ev P Rv) = Ev P Rv ∧
    0 < Ev P Rv ⬝ᵥ ((Cm P Rv)⁻¹ *ᵥ Ev P Rv) ∧ Ev P Rv ⬝ᵥ ((Cm P Rv)⁻¹ *ᵥ Ev P Rv) ≤ 1 := by
  have hdet : (Cm P Rv).det ≠ 0 := by
    intro h0
    obtain ⟨v, hv, hCv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
    have := Cm_pd hL2 hPD v hv
    rw [hCv, dotProduct_zero] at this
    exact lt_irrefl _ this
  have hinv : Cm P Rv *ᵥ ((Cm P Rv)⁻¹ *ᵥ Ev P Rv) = Ev P Rv := by
    rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hdet), one_mulVec]
  refine ⟨hinv, ?_, ?_⟩
  · have hl : Ev P Rv ⬝ᵥ ((Cm P Rv)⁻¹ *ᵥ Ev P Rv)
        = ((Cm P Rv)⁻¹ *ᵥ Ev P Rv) ⬝ᵥ (Cm P Rv *ᵥ ((Cm P Rv)⁻¹ *ᵥ Ev P Rv)) := by
      rw [hinv, dotProduct_comm]
    rw [hl]
    apply Cm_pd hL2 hPD
    intro h0
    apply hE
    rw [← hinv, h0, mulVec_zero]
  · have h2 := (G_moments hL2 hinv).2
    have hnn : 0 ≤ ∫ ω, (1 + ∑ j, (-((Cm P Rv)⁻¹ *ᵥ Ev P Rv)) j * Rv ω j) ^ 2 ∂P :=
      integral_nonneg fun ω => sq_nonneg _
    linarith

end Quad

lemma step_lower {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (Y : Ω → Fin d → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hXY : IndepFun X Y P)
    (F : ℝ → (Fin d → ℝ) → ℝ≥0∞) (hF : Measurable (fun p : ℝ × (Fin d → ℝ) => F p.1 p.2))
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) (hFg : ∀ x, g x ≤ ∫⁻ y, F x y ∂(P.map Y)) :
    ∫⁻ ω, g (X ω) ∂P ≤ ∫⁻ ω, F (X ω) (Y ω) ∂P := by
  have hmap := (indepFun_iff_map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable).1 hXY
  calc ∫⁻ ω, g (X ω) ∂P = ∫⁻ x, g x ∂(P.map X) := (lintegral_map hg hX).symm
    _ ≤ ∫⁻ x, ∫⁻ y, F x y ∂(P.map Y) ∂(P.map X) := lintegral_mono hFg
    _ = ∫⁻ p, F p.1 p.2 ∂((P.map X).prod (P.map Y)) := (lintegral_prod _ hF.aemeasurable).symm
    _ = ∫⁻ p, F p.1 p.2 ∂(P.map (fun ω => (X ω, Y ω))) := by rw [hmap]
    _ = ∫⁻ ω, F (X ω) (Y ω) ∂P := lintegral_map hF (hX.prodMk hY)

section Market

variable {Ω : Type*} [MeasurableSpace Ω] {d : ℕ}

noncomputable def W (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) : ℕ → Ω → ℝ
  | 0, _ => M.x0
  | n + 1, ω => (1 + M.i (n + 1)) * (W M π n ω + ∑ j, π n (W M π n ω) j * M.R (n + 1) ω j)

lemma W_succ (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) (n : ℕ) (ω : Ω) :
    W M π (n + 1) ω
      = (1 + M.i (n + 1)) * (W M π n ω + ∑ j, π n (W M π n ω) j * M.R (n + 1) ω j) := rfl

lemma tw_W (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) (k n : ℕ) (ω : Ω) :
    M.terminalWealth π k n (W M π n ω) ω = W M π (n + k) ω := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih =>
    show M.terminalWealth π k (n + 1)
      ((1 + M.i (n + 1)) * (W M π n ω + ∑ j, π n (W M π n ω) j * M.R (n + 1) ω j)) ω = _
    rw [← W_succ, ih (n + 1)]
    congr 1; omega

lemma tw0 (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) (ω : Ω) :
    M.terminalWealth π M.N 0 M.x0 ω = W M π M.N ω := by
  have h := tw_W M π M.N 0 ω
  rw [Nat.zero_add] at h
  exact h

lemma mean_W (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) :
    M.meanXN π = ∫ ω, W M π M.N ω ∂M.measIP := by
  unfold MVMarket.meanXN; simp only [tw0]

lemma meansq_W (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ)) :
    M.meanXNsq π = ∫ ω, W M π M.N ω ^ 2 ∂M.measIP := by
  unfold MVMarket.meanXNsq; simp only [tw0]

lemma S0_succ (M : MVMarket Ω d) (n : ℕ) : M.S0 (n + 1) = M.S0 n * (1 + M.i (n + 1)) := by
  unfold MVMarket.S0; exact Finset.prod_range_succ _ _

lemma S0_pos (M : MVMarket Ω d) (n : ℕ) (hn : n ≤ M.N) : 0 < M.S0 n := by
  unfold MVMarket.S0
  exact Finset.prod_pos fun k hk => M.hi_pos (k + 1) (by omega)
    (by have := Finset.mem_range.1 hk; omega)

lemma Ioc_prod (f : ℕ → ℝ) (N : ℕ) :
    ∏ k ∈ Finset.Ioc 0 N, f k = ∏ k ∈ Finset.range N, f (k + 1) := by
  induction N with
  | zero => simp
  | succ N ih => rw [Finset.prod_Ioc_succ_top (Nat.zero_le _), ih, Finset.prod_range_succ]

lemma dcoef_eq (M : MVMarket Ω d) :
    dcoef M 0 = ∏ k ∈ Finset.range M.N, (1 - M.ell (k + 1)) := Ioc_prod _ _

lemma mkt_facts (M : MVMarket Ω d) (n : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ M.N) :
    M.Cmat n *ᵥ ((M.Cmat n)⁻¹ *ᵥ M.Evec n) = M.Evec n ∧ 0 < M.ell n ∧ M.ell n ≤ 1 := by
  haveI := M.isProb
  exact ell_facts (M.hR_L2 n h1 h2) (M.hCov_posdef n h1 h2) (M.hR_mean_ne n h1 h2)

lemma dcoef_bounds (M : MVMarket Ω d) (hN : 1 ≤ M.N) : 0 ≤ dcoef M 0 ∧ dcoef M 0 < 1 := by
  rw [dcoef_eq]
  have hf' : ∀ k, k < M.N → 0 ≤ 1 - M.ell (k + 1) ∧ 1 - M.ell (k + 1) < 1 := by
    intro k hk
    obtain ⟨-, h1, h2⟩ := mkt_facts M (k + 1) (by omega) (by omega)
    constructor <;> linarith
  refine ⟨Finset.prod_nonneg fun k hk => (hf' k (Finset.mem_range.1 hk)).1, ?_⟩
  obtain ⟨N', hN'⟩ : ∃ N', M.N = N' + 1 := ⟨M.N - 1, by omega⟩
  rw [hN'] at hf' ⊢
  rw [Finset.prod_range_succ']
  apply mul_lt_one_of_nonneg_of_lt_one_right
  · exact Finset.prod_le_one (fun k hk => (hf' (k + 1) (by simp at hk; omega)).1)
      (fun k hk => (hf' (k + 1) (by simp at hk; omega)).2.le)
  · exact (hf' 0 (by omega)).1
  · exact (hf' 0 (by omega)).2

def mR (M : MVMarket Ω d) (k : Fin M.N) : MeasurableSpace Ω :=
  MeasurableSpace.comap (M.R (k.val + 1)) inferInstance

def Fn (M : MVMarket Ω d) (n : ℕ) : MeasurableSpace Ω :=
  ⨆ k ∈ {k : Fin M.N | k.val < n}, mR M k

lemma mR_le (M : MVMarket Ω d) (k : Fin M.N) : mR M k ≤ ‹MeasurableSpace Ω› :=
  (M.hR_meas (k.val + 1) (Nat.le_add_left 1 k.val) (Nat.succ_le_of_lt k.isLt)).comap_le

lemma Fn_le (M : MVMarket Ω d) (n : ℕ) : Fn M n ≤ ‹MeasurableSpace Ω› :=
  iSup₂_le fun k _ => mR_le M k

lemma Fn_mono (M : MVMarket Ω d) {m n : ℕ} (h : m ≤ n) : Fn M m ≤ Fn M n :=
  biSup_mono fun k hk => by simp only [Set.mem_setOf_eq] at hk ⊢; omega

lemma R_meas_F (M : MVMarket Ω d) (n : ℕ) (hn : n < M.N) :
    Measurable[Fn M (n + 1)] (M.R (n + 1)) := by
  rw [measurable_iff_comap_le]
  exact le_iSup₂_of_le (f := fun k (_ : k ∈ {k : Fin M.N | k.val < n + 1}) => mR M k)
    ⟨n, hn⟩ (by simp) le_rfl

lemma W_meas_F (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ))
    (hπ : ∀ k < M.N, Measurable (π k)) : ∀ n ≤ M.N, Measurable[Fn M n] (W M π n) := by
  intro n
  induction n with
  | zero =>
    intro _
    show Measurable[Fn M 0] (fun _ : Ω => M.x0)
    exact measurable_const
  | succ n ih =>
    intro hn
    have hW : Measurable[Fn M (n + 1)] (W M π n) :=
      (ih (by omega)).mono (Fn_mono M (Nat.le_succ n)) le_rfl
    have hR := R_meas_F M n (by omega)
    have hπn := hπ n (by omega)
    show Measurable[Fn M (n + 1)] (fun ω => (1 + M.i (n + 1)) *
      (W M π n ω + ∑ j, π n (W M π n ω) j * M.R (n + 1) ω j))
    exact measurable_const.mul (hW.add (Finset.measurable_sum _ fun j _ =>
      ((measurable_pi_apply j).comp (hπn.comp hW)).mul ((measurable_pi_apply j).comp hR)))

lemma W_meas (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ))
    (hπ : ∀ k < M.N, Measurable (π k)) (n : ℕ) (hn : n ≤ M.N) : Measurable (W M π n) :=
  (W_meas_F M π hπ n hn).mono (Fn_le M n) le_rfl

lemma W_indep (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ))
    (hπ : ∀ k < M.N, Measurable (π k)) (n : ℕ) (hn : n < M.N) :
    IndepFun (W M π n) (M.R (n + 1)) M.measIP := by
  have hI : iIndep (mR M) M.measIP := (iIndepFun_iff_iIndep _ _ _).1 M.hR_indep
  have hind := indep_iSup_of_disjoint (mR_le M) hI (S := {k : Fin M.N | k.val < n})
    (T := {⟨n, hn⟩}) (Set.disjoint_singleton_right.2 (by simp))
  rw [iSup_singleton] at hind
  rw [IndepFun_iff_Indep]
  exact indep_of_indep_of_le_left hind (measurable_iff_comap_le.1 (W_meas_F M π hπ n hn.le))

lemma lower_step (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ))
    (hπ : ∀ k < M.N, Measurable (π k)) (c : ℝ) (n : ℕ) (hn : n < M.N) :
    ENNReal.ofReal ((1 + M.i (n + 1)) ^ 2 * (1 - M.ell (n + 1))) *
        ∫⁻ ω, ENNReal.ofReal ((W M π n ω - c * M.S0 n) ^ 2) ∂M.measIP
      ≤ ∫⁻ ω, ENNReal.ofReal ((W M π (n + 1) ω - c * M.S0 (n + 1)) ^ 2) ∂M.measIP := by
  haveI := M.isProb
  have h1 : 1 ≤ n + 1 := by omega
  have h2 : n + 1 ≤ M.N := hn
  obtain ⟨hinv, -, hle⟩ := mkt_facts M (n + 1) h1 h2
  have hq0 : 0 ≤ (1 + M.i (n + 1)) ^ 2 * (1 - M.ell (n + 1)) :=
    mul_nonneg (sq_nonneg _) (by linarith)
  have hπn := hπ n hn
  have hRm := M.hR_meas (n + 1) h1 h2
  have hWm := W_meas M π hπ n hn.le
  have hL2 := M.hR_L2 (n + 1) h1 h2
  have hmeas : Measurable (fun ω => ENNReal.ofReal ((W M π n ω - c * M.S0 n) ^ 2)) := by
    fun_prop
  rw [← lintegral_const_mul _ hmeas]
  simp_rw [← ENNReal.ofReal_mul hq0]
  have hpt : ∀ ω, (W M π (n + 1) ω - c * M.S0 (n + 1)) ^ 2 = (1 + M.i (n + 1)) ^ 2 *
      ((W M π n ω - c * M.S0 n) + ∑ j, π n (W M π n ω) j * M.R (n + 1) ω j) ^ 2 := by
    intro ω; rw [W_succ, S0_succ]; ring
  simp_rw [hpt]
  have hFm : Measurable (fun p : ℝ × (Fin d → ℝ) => ENNReal.ofReal ((1 + M.i (n + 1)) ^ 2 *
      ((p.1 - c * M.S0 n) + ∑ j, π n p.1 j * p.2 j) ^ 2)) := by
    fun_prop
  refine step_lower M.measIP (W M π n) (M.R (n + 1)) hWm hRm (W_indep M π hπ n hn)
    (fun x y => ENNReal.ofReal ((1 + M.i (n + 1)) ^ 2 *
      ((x - c * M.S0 n) + ∑ j, π n x j * y j) ^ 2)) hFm
    (fun x => ENNReal.ofReal ((1 + M.i (n + 1)) ^ 2 * (1 - M.ell (n + 1)) *
      (x - c * M.S0 n) ^ 2)) (by fun_prop) ?_
  intro x
  rw [lintegral_map (by fun_prop) hRm]
  rw [← ofReal_integral_eq_lintegral_ofReal
    (((lin_memLp hL2 (x - c * M.S0 n) (π n x)).integrable_sq).const_mul _)
    (Filter.Eventually.of_forall fun ω => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  rw [integral_const_mul, quad hL2, mul_assoc]
  exact mul_le_mul_of_nonneg_left (quad_lower hL2 hinv (x - c * M.S0 n) (π n x)) (sq_nonneg _)

lemma lower_chain (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ))
    (hπ : ∀ k < M.N, Measurable (π k)) (c : ℝ) : ∀ n ≤ M.N,
    ENNReal.ofReal ((M.x0 - c) ^ 2 *
        ∏ k ∈ Finset.range n, ((1 + M.i (k + 1)) ^ 2 * (1 - M.ell (k + 1))))
      ≤ ∫⁻ ω, ENNReal.ofReal ((W M π n ω - c * M.S0 n) ^ 2) ∂M.measIP := by
  haveI := M.isProb
  intro n
  induction n with
  | zero =>
    intro _
    have h0 : ∀ ω, (W M π 0 ω - c * M.S0 0) ^ 2 = (M.x0 - c) ^ 2 := by
      intro ω; simp [W, MVMarket.S0]
    simp only [h0, Finset.prod_range_zero, mul_one]
    simp
  | succ n ih =>
    intro hn
    obtain ⟨-, -, hle⟩ := mkt_facts M (n + 1) (by omega) hn
    have hfac : 0 ≤ (1 + M.i (n + 1)) ^ 2 * (1 - M.ell (n + 1)) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    rw [Finset.prod_range_succ, ← mul_assoc, ENNReal.ofReal_mul' hfac, mul_comm]
    exact le_trans (mul_le_mul' le_rfl (ih (by omega))) (lower_step M π hπ c n (by omega))

lemma int_sq_sub {P : Measure Ω} [IsProbabilityMeasure P] {X : Ω → ℝ} (hX : MemLp X 2 P)
    (c : ℝ) : ∫ ω, (X ω - c) ^ 2 ∂P = ∫ ω, X ω ^ 2 ∂P - 2 * c * ∫ ω, X ω ∂P + c ^ 2 := by
  have h1 : Integrable X P := hX.integrable one_le_two
  have h2 : Integrable (fun ω => X ω ^ 2) P := hX.integrable_sq
  have : ∀ ω, (X ω - c) ^ 2 = X ω ^ 2 - 2 * c * X ω + c ^ 2 := fun ω => by ring
  have h3 : Integrable (fun ω => X ω ^ 2 - 2 * c * X ω) P := h2.sub (h1.const_mul (2 * c))
  simp_rw [this]
  rw [integral_add h3 (integrable_const _),
    integral_sub h2 (h1.const_mul (2 * c)), integral_const_mul]
  simp

lemma lower_bound (M : MVMarket Ω d) (π : ℕ → ℝ → (Fin d → ℝ))
    (hπ : ∀ k < M.N, Measurable (π k)) (hX : MemLp (W M π M.N) 2 M.measIP) (cT : ℝ) :
    dcoef M 0 * (M.x0 * M.S0 M.N - cT) ^ 2 ≤ ∫ ω, (W M π M.N ω - cT) ^ 2 ∂M.measIP := by
  haveI := M.isProb
  have hS := S0_pos M M.N le_rfl
  have h := lower_chain M π hπ (cT / M.S0 M.N) M.N le_rfl
  have e1 : ∀ ω, (W M π M.N ω - cT / M.S0 M.N * M.S0 M.N) = W M π M.N ω - cT := by
    intro ω; rw [div_mul_cancel₀ cT hS.ne']
  simp_rw [e1] at h
  have hI : Integrable (fun ω => (W M π M.N ω - cT) ^ 2) M.measIP :=
    (hX.sub (memLp_const cT)).integrable_sq
  rw [← ofReal_integral_eq_lintegral_ofReal hI
    (Filter.Eventually.of_forall fun ω => sq_nonneg _)] at h
  rw [ENNReal.ofReal_le_ofReal_iff (integral_nonneg fun ω => sq_nonneg _)] at h
  have hprod : ∏ k ∈ Finset.range M.N, ((1 + M.i (k + 1)) ^ 2 * (1 - M.ell (k + 1)))
      = M.S0 M.N ^ 2 * dcoef M 0 := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow, dcoef_eq]; rfl
  rw [hprod] at h
  have e2 : (M.x0 - cT / M.S0 M.N) * M.S0 M.N = M.x0 * M.S0 M.N - cT := by
    rw [sub_mul, div_mul_cancel₀ cT hS.ne']
  calc dcoef M 0 * (M.x0 * M.S0 M.N - cT) ^ 2
      = (M.x0 - cT / M.S0 M.N) ^ 2 * (M.S0 M.N ^ 2 * dcoef M 0) := by rw [← e2]; ring
    _ ≤ _ := h

lemma var_lower (M : MVMarket Ω d) (hN : 1 ≤ M.N) (π : ℕ → ℝ → (Fin d → ℝ))
    (hadm : M.IsAdmissible 0 π) (hm : M.μ ≤ M.meanXN π) :
    dcoef M 0 / (1 - dcoef M 0) * (M.μ - M.x0 * M.S0 M.N) ^ 2 ≤ M.varXN π := by
  haveI := M.isProb
  have hadm' : (∀ k, 0 ≤ k → k < M.N → Measurable (π k)) ∧
      MemLp (fun ω => M.terminalWealth π (M.N - 0) 0 M.x0 ω) 2 M.measIP := hadm
  obtain ⟨hπ, hX⟩ := hadm'
  simp only [Nat.sub_zero, tw0] at hX
  have hπ' : ∀ k < M.N, Measurable (π k) := fun k hk => hπ k (Nat.zero_le k) hk
  obtain ⟨hd0, hd1⟩ := dcoef_bounds M hN
  have hμa : M.x0 * M.S0 M.N < M.μ := M.hμ
  have hmW := mean_W M π
  have hsq := meansq_W M π
  have hvar : M.varXN π = ∫ ω, W M π M.N ω ^ 2 ∂M.measIP - (M.meanXN π) ^ 2 := by
    unfold MVMarket.varXN; rw [hsq]
  obtain ⟨c, hcdef⟩ : ∃ c, c = (M.meanXN π - dcoef M 0 * (M.x0 * M.S0 M.N)) / (1 - dcoef M 0) :=
    ⟨_, rfl⟩
  have hlb := lower_bound M π hπ' hX c
  have hc := int_sq_sub hX c
  rw [← hmW] at hc
  have h1d : 0 < 1 - dcoef M 0 := by linarith
  have h1dne : 1 - dcoef M 0 ≠ 0 := h1d.ne'
  have key : dcoef M 0 * (M.x0 * M.S0 M.N - c) ^ 2 - (M.meanXN π - c) ^ 2
      = dcoef M 0 / (1 - dcoef M 0) * (M.meanXN π - M.x0 * M.S0 M.N) ^ 2 := by
    rw [hcdef]; field_simp; ring
  have hmono : (M.μ - M.x0 * M.S0 M.N) ^ 2 ≤ (M.meanXN π - M.x0 * M.S0 M.N) ^ 2 := by
    nlinarith
  have hcoef : 0 ≤ dcoef M 0 / (1 - dcoef M 0) := div_nonneg hd0 h1d.le
  have hfin := mul_le_mul_of_nonneg_left hmono hcoef
  rw [hvar]
  nlinarith

noncomputable def pstar (M : MVMarket Ω d) (K : ℝ) : ℕ → ℝ → (Fin d → ℝ) := fun n x =>
  (K * (M.S0 n / M.S0 M.N) - x) • (M.Cmat (n + 1))⁻¹.mulVec (M.Evec (n + 1))

lemma pstar_meas (M : MVMarket Ω d) (K : ℝ) (k : ℕ) : Measurable (pstar M K k) := by
  unfold pstar; fun_prop

noncomputable def hv (M : MVMarket Ω d) (n : ℕ) : Fin d → ℝ := (M.Cmat n)⁻¹ *ᵥ M.Evec n

noncomputable def Gf (M : MVMarket Ω d) (n : ℕ) (ω : Ω) : ℝ :=
  1 + ∑ j, (-hv M n) j * M.R n ω j

noncomputable def Dst (M : MVMarket Ω d) (K : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  W M (pstar M K) n ω - K * (M.S0 n / M.S0 M.N)

lemma Dst_meas (M : MVMarket Ω d) (K : ℝ) (n : ℕ) (hn : n ≤ M.N) : Measurable (Dst M K n) :=
  (W_meas M (pstar M K) (fun k _ => pstar_meas M K k) n hn).sub_const _

lemma star_step (M : MVMarket Ω d) (K : ℝ) (n : ℕ) (ω : Ω) :
    Dst M K (n + 1) ω = (1 + M.i (n + 1)) * (Dst M K n ω * Gf M (n + 1) ω) := by
  have hsum : ∑ j, pstar M K n (W M (pstar M K) n ω) j * M.R (n + 1) ω j
      = (K * (M.S0 n / M.S0 M.N) - W M (pstar M K) n ω) *
        ∑ j, hv M (n + 1) j * M.R (n + 1) ω j := by
    rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun j _ => ?_
    simp only [pstar, hv, Pi.smul_apply, smul_eq_mul]; ring
  have hG : Gf M (n + 1) ω = 1 - ∑ j, hv M (n + 1) j * M.R (n + 1) ω j := by
    simp only [Gf, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]; ring
  rw [hG]
  simp only [Dst]
  rw [W_succ, hsum, S0_succ]
  ring

lemma star_moments (M : MVMarket Ω d) (K : ℝ) : ∀ n ≤ M.N,
    Integrable (fun ω => Dst M K n ω ^ 2) M.measIP ∧
    ∫ ω, Dst M K n ω ∂M.measIP = (M.x0 - K * (M.S0 0 / M.S0 M.N)) *
      ∏ k ∈ Finset.range n, ((1 + M.i (k + 1)) * (1 - M.ell (k + 1))) ∧
    ∫ ω, Dst M K n ω ^ 2 ∂M.measIP = (M.x0 - K * (M.S0 0 / M.S0 M.N)) ^ 2 *
      ∏ k ∈ Finset.range n, ((1 + M.i (k + 1)) ^ 2 * (1 - M.ell (k + 1))) := by
  haveI := M.isProb
  intro n
  induction n with
  | zero =>
    intro _
    have h0 : ∀ ω, Dst M K 0 ω = M.x0 - K * (M.S0 0 / M.S0 M.N) := fun ω => rfl
    simp only [h0, Finset.prod_range_zero, mul_one]
    refine ⟨integrable_const _, ?_, ?_⟩ <;> simp
  | succ n ih =>
    intro hn
    obtain ⟨hI, hm1, hm2⟩ := ih (by omega)
    have h1 : 1 ≤ n + 1 := by omega
    have h2 : n + 1 ≤ M.N := hn
    obtain ⟨hinv, -, -⟩ := mkt_facts M (n + 1) h1 h2
    have hL2 := M.hR_L2 (n + 1) h1 h2
    have hRm := M.hR_meas (n + 1) h1 h2
    have hDm : Measurable (Dst M K n) := Dst_meas M K n (by omega)
    have hGm : Measurable (Gf M (n + 1)) := by
      unfold Gf
      exact measurable_const.add (Finset.measurable_sum _ fun j _ =>
        measurable_const.mul ((measurable_pi_apply j).comp hRm))
    have hind := W_indep M (pstar M K) (fun k _ => pstar_meas M K k) n (by omega)
    have hψ : Measurable (fun r : Fin d → ℝ => 1 + ∑ j, (-hv M (n + 1)) j * r j) :=
      measurable_const.add (Finset.measurable_sum _ fun j _ =>
        measurable_const.mul (measurable_pi_apply j))
    have hDG : IndepFun (Dst M K n) (Gf M (n + 1)) M.measIP :=
      hind.comp (φ := fun x => x - K * (M.S0 n / M.S0 M.N))
        (ψ := fun r : Fin d → ℝ => 1 + ∑ j, (-hv M (n + 1)) j * r j) (measurable_id.sub_const _) hψ
    have hDG2 : IndepFun (fun ω => Dst M K n ω ^ 2) (fun ω => Gf M (n + 1) ω ^ 2) M.measIP :=
      hDG.comp (φ := fun x => x ^ 2) (ψ := fun x => x ^ 2)
        (measurable_id.pow_const 2) (measurable_id.pow_const 2)
    have hGmom := G_moments hL2 hinv
    have hG1 : ∫ ω, Gf M (n + 1) ω ∂M.measIP = 1 - M.ell (n + 1) := hGmom.1
    have hG2 : ∫ ω, Gf M (n + 1) ω ^ 2 ∂M.measIP = 1 - M.ell (n + 1) := hGmom.2
    have hG2i : Integrable (fun ω => Gf M (n + 1) ω ^ 2) M.measIP :=
      (lin_memLp hL2 1 (-hv M (n + 1))).integrable_sq
    refine ⟨?_, ?_, ?_⟩
    · refine ((hDG2.integrable_mul hI hG2i).const_mul ((1 + M.i (n + 1)) ^ 2)).congr
        (Filter.Eventually.of_forall fun ω => ?_)
      simp only [Pi.mul_apply]; rw [star_step]; ring
    · simp_rw [star_step M K n]
      rw [integral_const_mul, hDG.integral_fun_mul_eq_mul_integral hDm.aestronglyMeasurable
        hGm.aestronglyMeasurable, hm1, hG1, Finset.prod_range_succ]
      ring
    · simp_rw [star_step M K n, mul_pow]
      rw [integral_const_mul, hDG2.integral_fun_mul_eq_mul_integral
        (hDm.pow_const 2).aestronglyMeasurable (hGm.pow_const 2).aestronglyMeasurable,
        hm2, hG2, Finset.prod_range_succ]
      ring

lemma star_main (M : MVMarket Ω d) (K : ℝ) :
    M.IsAdmissible 0 (pstar M K) ∧
    M.meanXN (pstar M K) = (M.x0 * M.S0 M.N - K) * dcoef M 0 + K ∧
    M.varXN (pstar M K) = (M.x0 * M.S0 M.N - K) ^ 2 * dcoef M 0 * (1 - dcoef M 0) := by
  haveI := M.isProb
  have hS : 0 < M.S0 M.N := S0_pos M M.N le_rfl
  have hSne : M.S0 M.N ≠ 0 := hS.ne'
  have hS00 : M.S0 0 = 1 := by simp [MVMarket.S0]
  obtain ⟨hI2, hm1, hm2⟩ := star_moments M K M.N le_rfl
  have hprod1 : ∏ k ∈ Finset.range M.N, ((1 + M.i (k + 1)) * (1 - M.ell (k + 1)))
      = M.S0 M.N * dcoef M 0 := by
    rw [Finset.prod_mul_distrib, dcoef_eq]; rfl
  have hprod2 : ∏ k ∈ Finset.range M.N, ((1 + M.i (k + 1)) ^ 2 * (1 - M.ell (k + 1)))
      = M.S0 M.N ^ 2 * dcoef M 0 := by
    rw [Finset.prod_mul_distrib, Finset.prod_pow, dcoef_eq]; rfl
  rw [hprod1, hS00] at hm1
  rw [hprod2, hS00] at hm2
  have hDm : Measurable (Dst M K M.N) := Dst_meas M K M.N le_rfl
  have hDL2 : MemLp (Dst M K M.N) 2 M.measIP :=
    (memLp_two_iff_integrable_sq hDm.aestronglyMeasurable).2 hI2
  have hWeq : W M (pstar M K) M.N = fun ω => Dst M K M.N ω + K := by
    funext ω; simp only [Dst, div_self hSne]; ring
  have hWL2 : MemLp (W M (pstar M K) M.N) 2 M.measIP := by
    rw [hWeq]; exact hDL2.add (memLp_const K)
  have hmean := mean_W M (pstar M K)
  have hsq := meansq_W M (pstar M K)
  have hWint : ∫ ω, W M (pstar M K) M.N ω ∂M.measIP = ∫ ω, Dst M K M.N ω ∂M.measIP + K := by
    rw [hWeq, integral_add (hDL2.integrable one_le_two) (integrable_const K)]; simp
  have hc := int_sq_sub hWL2 K
  have hDK : ∫ ω, (W M (pstar M K) M.N ω - K) ^ 2 ∂M.measIP
      = ∫ ω, Dst M K M.N ω ^ 2 ∂M.measIP := by
    rw [hWeq]; simp
  rw [hWint, hm1] at hc
  have e1 : ∫ ω, W M (pstar M K) M.N ω ^ 2 ∂M.measIP
      = (M.x0 - K * (1 / M.S0 M.N)) ^ 2 * (M.S0 M.N ^ 2 * dcoef M 0)
        + 2 * K * ((M.x0 - K * (1 / M.S0 M.N)) * (M.S0 M.N * dcoef M 0) + K) - K ^ 2 := by
    linear_combination -hc + hDK + hm2
  refine ⟨?_, ?_, ?_⟩
  · show (∀ k, 0 ≤ k → k < M.N → Measurable (pstar M K k)) ∧
      MemLp (fun ω => M.terminalWealth (pstar M K) (M.N - 0) 0 M.x0 ω) 2 M.measIP
    refine ⟨fun k _ _ => pstar_meas M K k, ?_⟩
    simp only [Nat.sub_zero, tw0]
    exact hWL2
  · rw [hmean, hWint, hm1]; field_simp
  · unfold MVMarket.varXN
    rw [hsq, hmean, e1, hWint, hm1]
    field_simp; ring

end Market

end MV466

open MDPFinance.MeanVariance BauerleRiederMDP.MeanVariance in
theorem solution {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (M : MVMarket Ω d)
    (hN : 1 ≤ M.N) :
    let πstar : ℕ → ℝ → (Fin d → ℝ) := fun n x =>
      ((M.μ - dcoef M 0 * M.x0 * M.S0 M.N) / (1 - dcoef M 0) * (M.S0 n / M.S0 M.N) - x) •
        (M.Cmat (n + 1))⁻¹.mulVec (M.Evec (n + 1))
    M.IsOptimalMV πstar ∧
      M.meanXN πstar = M.μ ∧
      M.varXN πstar = dcoef M 0 / (1 - dcoef M 0) * (M.meanXN πstar - M.x0 * M.S0 M.N) ^ 2 ∧
      (⨅ π : {π : ℕ → ℝ → (Fin d → ℝ) // M.IsAdmissible 0 π ∧ M.μ ≤ M.meanXN π},
        M.varXN π.1) = M.varXN πstar := by
  intro πstar
  obtain ⟨hd0, hd1⟩ := MV466.dcoef_bounds M hN
  have h1d : 1 - dcoef M 0 ≠ 0 := (by linarith : (0 : ℝ) < 1 - dcoef M 0).ne'
  have hπs : πstar = MV466.pstar M ((M.μ - dcoef M 0 * M.x0 * M.S0 M.N) / (1 - dcoef M 0)) :=
    rfl
  obtain ⟨hadm, hmean, hvar⟩ :=
    MV466.star_main M ((M.μ - dcoef M 0 * M.x0 * M.S0 M.N) / (1 - dcoef M 0))
  rw [← hπs] at hadm hmean hvar
  have hmean' : M.meanXN πstar = M.μ := by
    rw [hmean]; field_simp; ring
  have hvar' : M.varXN πstar = dcoef M 0 / (1 - dcoef M 0) * (M.μ - M.x0 * M.S0 M.N) ^ 2 := by
    rw [hvar]; field_simp; ring
  have hlow := MV466.var_lower M hN
  have hopt : M.IsOptimalMV πstar :=
    ⟨hadm, hmean'.ge, fun π h1 h2 => by rw [hvar']; exact hlow π h1 h2⟩
  refine ⟨hopt, hmean', by rw [hvar', hmean'], ?_⟩
  apply le_antisymm
  · exact ciInf_le ⟨M.varXN πstar, by
      rintro _ ⟨π, rfl⟩; rw [hvar']; exact hlow π.1 π.2.1 π.2.2⟩
      (⟨πstar, hadm, hmean'.ge⟩ :
        {π : ℕ → ℝ → (Fin d → ℝ) // M.IsAdmissible 0 π ∧ M.μ ≤ M.meanXN π})
  · haveI : Nonempty {π : ℕ → ℝ → (Fin d → ℝ) // M.IsAdmissible 0 π ∧ M.μ ≤ M.meanXN π} :=
      ⟨⟨πstar, hadm, hmean'.ge⟩⟩
    exact le_ciInf fun π => by rw [hvar']; exact hlow π.1 π.2.1 π.2.2
