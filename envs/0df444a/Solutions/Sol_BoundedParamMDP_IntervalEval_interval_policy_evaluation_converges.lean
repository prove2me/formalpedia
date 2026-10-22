-- Prove2me | solution 1 for BoundedParamMDP.IntervalEval.interval_policy_evaluation_converges
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T11:32:08.29522+00:00
-- url     : https://prove2.me/submissions/58b5bb8c-b81b-4b89-aad5-3ad860a20dd7

import Mathlib
import Definitions.Def_BoundedParamMDP_Optimal_MDP
import Definitions.Def_BoundedParamMDP_Optimal_BMDP
import Definitions.Def_BoundedParamMDP_IntervalEval_IntervalPolicyEvaluation

set_option autoImplicit false

open Matrix

theorem bpm66_row_abs {Q : Type*} [Fintype Q] (f w : Q → ℝ) (c : ℝ)
    (hf0 : ∀ q, 0 ≤ f q) (hf1 : ∑ q, f q = 1) (hw : ∀ q, |w q| ≤ c) :
    |∑ q, f q * w q| ≤ c := by
  calc |∑ q, f q * w q| ≤ ∑ q, |f q * w q| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ q, f q * c := by
        apply Finset.sum_le_sum
        intro q _
        rw [abs_mul, abs_of_nonneg (hf0 q)]
        exact mul_le_mul_of_nonneg_left (hw q) (hf0 q)
    _ = c := by rw [← Finset.sum_mul, hf1, one_mul]

theorem bpm66_row_mono {Q : Type*} [Fintype Q] (f u v : Q → ℝ)
    (hf0 : ∀ q, 0 ≤ f q) (huv : u ≤ v) : ∑ q, f q * u q ≤ ∑ q, f q * v q :=
  Finset.sum_le_sum fun q _ => mul_le_mul_of_nonneg_left (huv q) (hf0 q)

open BoundedParamMDP.Optimal in
/-- The admissible rows at `(p, α)`. -/
def bpm66S {Q A : Type*} [Fintype Q] (B : BMDP Q A) (p : Q) (α : A) : Set (Q → ℝ) :=
  Set.Icc (B.lo p α) (B.hi p α) ∩ {f | ∑ q, f q = 1}

open BoundedParamMDP.Optimal in
theorem bpm66S_nonempty {Q A : Type*} [Fintype Q] (B : BMDP Q A) (p : Q) (α : A) :
    (bpm66S B p α).Nonempty := by
  let g : ℝ → ℝ := fun t => ∑ q, (B.lo p α q + t * (B.hi p α q - B.lo p α q))
  have hg : ContinuousOn g (Set.Icc 0 1) := by
    apply Continuous.continuousOn
    fun_prop
  have h01 : (1:ℝ) ∈ Set.Icc (g 0) (g 1) := by
    simp only [g, zero_mul, add_zero, one_mul, add_sub_cancel]
    exact ⟨B.sum_lo_le_one p α, B.one_le_sum_hi p α⟩
  obtain ⟨t, ⟨ht0, ht1⟩, hgt⟩ := intermediate_value_Icc zero_le_one hg h01
  refine ⟨fun q => B.lo p α q + t * (B.hi p α q - B.lo p α q), ⟨⟨fun q => ?_, fun q => ?_⟩, hgt⟩⟩
  · have := B.lo_le_hi p α q
    show B.lo p α q ≤ B.lo p α q + t * (B.hi p α q - B.lo p α q)
    nlinarith
  · have := B.lo_le_hi p α q
    show B.lo p α q + t * (B.hi p α q - B.lo p α q) ≤ B.hi p α q
    nlinarith

open BoundedParamMDP.Optimal in
theorem bpm66S_compact {Q A : Type*} [Fintype Q] (B : BMDP Q A) (p : Q) (α : A) :
    IsCompact (bpm66S B p α) :=
  isCompact_Icc.inter_right (isClosed_eq (by fun_prop) continuous_const)

open BoundedParamMDP.Optimal in
theorem bpm66S_min {Q A : Type*} [Fintype Q] (B : BMDP Q A) (p : Q) (α : A) (u : Q → ℝ) :
    ∃ f ∈ bpm66S B p α, ∀ g ∈ bpm66S B p α, ∑ q, f q * u q ≤ ∑ q, g q * u q := by
  obtain ⟨f, hf, hmin⟩ := (bpm66S_compact B p α).exists_isMinOn (bpm66S_nonempty B p α)
    (Continuous.continuousOn (f := fun f : Q → ℝ => ∑ q, f q * u q) (by fun_prop))
  exact ⟨f, hf, fun g hg => isMinOn_iff.1 hmin g hg⟩

open BoundedParamMDP.Optimal in
theorem bpm66S_max {Q A : Type*} [Fintype Q] (B : BMDP Q A) (p : Q) (α : A) (u : Q → ℝ) :
    ∃ f ∈ bpm66S B p α, ∀ g ∈ bpm66S B p α, ∑ q, g q * u q ≤ ∑ q, f q * u q := by
  obtain ⟨f, hf, hmax⟩ := (bpm66S_compact B p α).exists_isMaxOn (bpm66S_nonempty B p α)
    (Continuous.continuousOn (f := fun f : Q → ℝ => ∑ q, f q * u q) (by fun_prop))
  exact ⟨f, hf, fun g hg => isMaxOn_iff.1 hmax g hg⟩

open BoundedParamMDP.Optimal in
/-- The member MDP with the given rows. -/
noncomputable def bpm66Mk {Q A : Type*} [Fintype Q] (B : BMDP Q A) (F : Q → A → Q → ℝ)
    (hF : ∀ p α, F p α ∈ bpm66S B p α) : Member B :=
  ⟨{ F := F
     F_nonneg := fun p α q => le_trans (B.lo_nonneg p α q) ((hF p α).1.1 q)
     F_sum := fun p α => (hF p α).2
     R := B.R
     γ := B.γ
     γ_nonneg := B.γ_nonneg
     γ_lt_one := B.γ_lt_one }, rfl, rfl, fun p α q => ⟨(hF p α).1.1 q, (hF p α).1.2 q⟩⟩

open BoundedParamMDP.Optimal in
theorem bpm66_row_mem {Q A : Type*} [Fintype Q] {B : BMDP Q A} (M : Member B) (p : Q) (α : A) :
    M.1.F p α ∈ bpm66S B p α :=
  ⟨⟨fun q => (M.2.2.2 p α q).1, fun q => (M.2.2.2 p α q).2⟩, M.1.F_sum p α⟩

open BoundedParamMDP.Optimal in
theorem bpm66_VIpol_mem {Q A : Type*} [Fintype Q] {B : BMDP Q A} (M : Member B)
    (π : Policy Q A) (v : Q → ℝ) (p : Q) :
    VIpol M.1 π v p = B.R p + B.γ * ∑ q, M.1.F p (π p) q * v q := by
  unfold VIpol
  rw [M.2.1, M.2.2.1]

open BoundedParamMDP.Optimal in
theorem bpm66_VIpol_lip {Q A : Type*} [Fintype Q] (M : MDP Q A) (π : Policy Q A)
    (u v : Q → ℝ) (p : Q) :
    |VIpol M π u p - VIpol M π v p| ≤ M.γ * dist u v := by
  have h := bpm66_row_abs (M.F p (π p)) (fun q => u q - v q) (dist u v)
    (M.F_nonneg p (π p)) (M.F_sum p (π p))
    (fun q => by rw [← Real.dist_eq]; exact dist_le_pi_dist u v q)
  have e : VIpol M π u p - VIpol M π v p = M.γ * ∑ q, M.F p (π p) q * (u q - v q) := by
    unfold VIpol
    simp only [mul_sub, Finset.sum_sub_distrib]
    ring
  rw [e, abs_mul, abs_of_nonneg M.γ_nonneg]
  exact mul_le_mul_of_nonneg_left h M.γ_nonneg

open BoundedParamMDP.Optimal in
theorem bpm66_VIpol_mono {Q A : Type*} [Fintype Q] (M : MDP Q A) (π : Policy Q A)
    {u v : Q → ℝ} (huv : u ≤ v) : VIpol M π u ≤ VIpol M π v := by
  intro p
  unfold VIpol
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left
    (bpm66_row_mono _ _ _ (M.F_nonneg p (π p)) huv) M.γ_nonneg)

/-! ### Exact-MDP value facts -/

open BoundedParamMDP.Optimal in
theorem bpm66_mulVec_chain {Q A : Type*} [Fintype Q] (M : MDP Q A) (π : Policy Q A)
    (w : Q → ℝ) (p : Q) :
    (chainMatrix M π *ᵥ w) p = ∑ q, M.F p (π p) q * w q := rfl

open BoundedParamMDP.Optimal in
theorem bpm66_pow_bound {Q A : Type*} [Fintype Q] [DecidableEq Q] (M : MDP Q A)
    (π : Policy Q A) (t : ℕ) : ∀ p : Q, |((chainMatrix M π ^ t) *ᵥ M.R) p| ≤ ‖M.R‖ := by
  induction t with
  | zero =>
    intro p
    rw [pow_zero, Matrix.one_mulVec, ← Real.norm_eq_abs]
    exact norm_le_pi_norm M.R p
  | succ t ih =>
    intro p
    rw [pow_succ', ← Matrix.mulVec_mulVec, bpm66_mulVec_chain]
    exact bpm66_row_abs _ _ _ (M.F_nonneg p (π p)) (M.F_sum p (π p)) ih

open BoundedParamMDP.Optimal in
theorem bpm66_summable {Q A : Type*} [Fintype Q] [DecidableEq Q] (M : MDP Q A)
    (π : Policy Q A) (p : Q) :
    Summable (fun t : ℕ => M.γ ^ t * ((chainMatrix M π ^ t) *ᵥ M.R) p) := by
  refine Summable.of_norm_bounded (g := fun t : ℕ => ‖M.R‖ * M.γ ^ t)
    ((summable_geometric_of_lt_one M.γ_nonneg M.γ_lt_one).mul_left _) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg M.γ_nonneg t), mul_comm]
  exact mul_le_mul_of_nonneg_right (bpm66_pow_bound M π t p) (pow_nonneg M.γ_nonneg t)

open BoundedParamMDP.Optimal in
theorem bpm66_value_fix {Q A : Type*} [Fintype Q] [DecidableEq Q] (M : MDP Q A)
    (π : Policy Q A) : VIpol M π (value M π) = value M π := by
  funext p
  have hs := fun q => bpm66_summable M π q
  have e : ∀ t : ℕ, M.γ ^ (t + 1) * ((chainMatrix M π ^ (t + 1)) *ᵥ M.R) p
      = ∑ q, M.γ * M.F p (π p) q * (M.γ ^ t * ((chainMatrix M π ^ t) *ᵥ M.R) q) := by
    intro t
    rw [pow_succ', pow_succ', ← Matrix.mulVec_mulVec, bpm66_mulVec_chain, Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  have hshift : HasSum (fun t : ℕ => M.γ ^ (t + 1) * ((chainMatrix M π ^ (t + 1)) *ᵥ M.R) p)
      (M.γ * ∑ q, M.F p (π p) q * value M π q) := by
    have hfun : (fun t : ℕ => M.γ ^ (t + 1) * ((chainMatrix M π ^ (t + 1)) *ᵥ M.R) p)
        = fun t : ℕ => ∑ q, M.γ * M.F p (π p) q * (M.γ ^ t * ((chainMatrix M π ^ t) *ᵥ M.R) q) :=
      funext e
    rw [hfun, Finset.mul_sum]
    refine hasSum_sum fun q _ => ?_
    rw [← mul_assoc]
    exact (hs q).hasSum.mul_left (M.γ * M.F p (π p) q)
  have h0 : HasSum (fun t : ℕ => M.γ ^ t * ((chainMatrix M π ^ t) *ᵥ M.R) p)
      (M.R p + M.γ * ∑ q, M.F p (π p) q * value M π q) := by
    rw [← hasSum_nat_add_iff' 1]
    simp only [Finset.sum_range_one, pow_zero, one_mul, Matrix.one_mulVec, add_sub_cancel_left]
    exact hshift
  show M.R p + M.γ * ∑ q, M.F p (π p) q * value M π q = value M π p
  exact h0.unique (hs p).hasSum

open BoundedParamMDP.Optimal in
theorem bpm66_fix_unique {Q A : Type*} [Fintype Q] [DecidableEq Q] (M : MDP Q A)
    (π : Policy Q A) (v : Q → ℝ) (hv : VIpol M π v = v) : v = value M π := by
  have hV := bpm66_value_fix M π
  have key : dist v (value M π) ≤ M.γ * dist v (value M π) := by
    refine (dist_pi_le_iff (mul_nonneg M.γ_nonneg dist_nonneg)).2 fun p => ?_
    have h := bpm66_VIpol_lip M π v (value M π) p
    rw [hv, hV, ← Real.dist_eq] at h
    exact h
  have hd := dist_nonneg (x := v) (y := value M π)
  have h1 := M.γ_lt_one
  have h0 : dist v (value M π) ≤ 0 := by nlinarith
  exact dist_le_zero.1 h0

/-! ### Lower bound -/

open BoundedParamMDP.Optimal in
theorem bpm66_attain_lo {Q A : Type*} [Fintype Q] (B : BMDP Q A) (π : Policy Q A)
    (u : Q → ℝ) : ∃ M : Member B, ∀ (M' : Member B) p, VIpol M.1 π u p ≤ VIpol M'.1 π u p := by
  have h := fun p α => bpm66S_min B p α u
  choose F hF hmin using h
  refine ⟨bpm66Mk B F hF, fun M' p => ?_⟩
  rw [bpm66_VIpol_mem, bpm66_VIpol_mem]
  have := hmin p (π p) _ (bpm66_row_mem M' p (π p))
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left this B.γ_nonneg)

open BoundedParamMDP.Optimal BoundedParamMDP.IntervalEval in
theorem bpm66_IVIlo_eq {Q A : Type*} [Fintype Q] (B : BMDP Q A) (π : Policy Q A)
    (u : Q → ℝ) (M : Member B) (hM : ∀ (M' : Member B) p, VIpol M.1 π u p ≤ VIpol M'.1 π u p)
    (p : Q) : IVIlo B π u p = VIpol M.1 π u p := by
  unfold IVIlo
  haveI : Nonempty (Member B) := ⟨M⟩
  apply le_antisymm
  · have hb : BddBelow (Set.range fun M' : Member B => VIpol M'.1 π u p) := by
      refine ⟨VIpol M.1 π u p, ?_⟩
      rintro _ ⟨M', rfl⟩
      exact hM M' p
    exact ciInf_le hb M
  · exact le_ciInf fun M' => hM M' p

open BoundedParamMDP.Optimal BoundedParamMDP.IntervalEval in
theorem bpm66_lo_le {Q A : Type*} [Fintype Q] (B : BMDP Q A) (π : Policy Q A)
    (u : Q → ℝ) (M' : Member B) (p : Q) : IVIlo B π u p ≤ VIpol M'.1 π u p := by
  obtain ⟨M, hM⟩ := bpm66_attain_lo B π u
  rw [bpm66_IVIlo_eq B π u M hM p]
  exact hM M' p

open BoundedParamMDP.Optimal BoundedParamMDP.IntervalEval in
theorem bpm66_lo_mono {Q A : Type*} [Fintype Q] (B : BMDP Q A) (π : Policy Q A)
    {u v : Q → ℝ} (huv : u ≤ v) : IVIlo B π u ≤ IVIlo B π v := by
  intro p
  obtain ⟨Mu, hMu⟩ := bpm66_attain_lo B π u
  obtain ⟨Mv, hMv⟩ := bpm66_attain_lo B π v
  rw [bpm66_IVIlo_eq B π u Mu hMu p, bpm66_IVIlo_eq B π v Mv hMv p]
  exact le_trans (hMu Mv p) (bpm66_VIpol_mono Mv.1 π huv p)

open BoundedParamMDP.Optimal BoundedParamMDP.IntervalEval in
theorem bpm66_lo_contr {Q A : Type*} [Fintype Q] (B : BMDP Q A) (π : Policy Q A) :
    ContractingWith (Real.toNNReal B.γ) (IVIlo B π) := by
  refine ⟨Real.toNNReal_lt_one.2 B.γ_lt_one, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  rw [Real.coe_toNNReal _ B.γ_nonneg]
  refine (dist_pi_le_iff (mul_nonneg B.γ_nonneg dist_nonneg)).2 fun p => ?_
  obtain ⟨Mu, hMu⟩ := bpm66_attain_lo B π u
  obtain ⟨Mv, hMv⟩ := bpm66_attain_lo B π v
  rw [Real.dist_eq, bpm66_IVIlo_eq B π u Mu hMu p, bpm66_IVIlo_eq B π v Mv hMv p, abs_le]
  have h1 := hMu Mv p
  have h2 := hMv Mu p
  have h3 := abs_le.1 (bpm66_VIpol_lip Mu.1 π u v p)
  have h4 := abs_le.1 (bpm66_VIpol_lip Mv.1 π u v p)
  rw [Mu.2.2.1] at h3
  rw [Mv.2.2.1] at h4
  constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]

open BoundedParamMDP.Optimal BoundedParamMDP.IntervalEval in
theorem bpm66_lower {Q A : Type*} [Fintype Q] [DecidableEq Q] (B : BMDP Q A)
    (π : Policy Q A) (V₀ : Q → ℝ) :
    Filter.Tendsto (fun n : ℕ => (IVIlo B π)^[n] V₀) Filter.atTop (nhds (lowerV B π)) := by
  have hc := bpm66_lo_contr B π
  obtain ⟨L, hfix, hT⟩ : ∃ L, IVIlo B π L = L ∧
      ∀ x, Filter.Tendsto (fun n : ℕ => (IVIlo B π)^[n] x) Filter.atTop (nhds L) :=
    ⟨_, ContractingWith.fixedPoint_isFixedPt hc,
      fun x => ContractingWith.tendsto_iterate_fixedPoint hc x⟩
  obtain ⟨Ms, hMs⟩ := bpm66_attain_lo B π L
  have hVs : VIpol Ms.1 π L = L := by
    funext p
    rw [← bpm66_IVIlo_eq B π L Ms hMs p, hfix]
  have hLval : L = value Ms.1 π := bpm66_fix_unique Ms.1 π L hVs
  have hle : ∀ M : Member B, L ≤ value M.1 π := by
    intro M
    have h1 : IVIlo B π (value M.1 π) ≤ value M.1 π := fun p => by
      have := bpm66_lo_le B π (value M.1 π) M p
      rwa [bpm66_value_fix] at this
    have h2 : ∀ n : ℕ, (IVIlo B π)^[n] (value M.1 π) ≤ value M.1 π := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact le_trans (bpm66_lo_mono B π ih) h1
    exact le_of_tendsto' (hT (value M.1 π)) h2
  have hlow : lowerV B π = L := by
    funext q
    haveI : Nonempty (Member B) := ⟨Ms⟩
    unfold lowerV
    apply le_antisymm
    · have hb : BddBelow (Set.range fun M : Member B => value M.1 π q) := by
        refine ⟨L q, ?_⟩
        rintro _ ⟨M, rfl⟩
        exact hle M q
      refine le_trans (ciInf_le hb Ms) ?_
      rw [hLval]
    · exact le_ciInf fun M => hle M q
  rw [hlow]
  exact hT V₀

/-! ### Upper bound -/

open BoundedParamMDP.Optimal in
theorem bpm66_attain_hi {Q A : Type*} [Fintype Q] (B : BMDP Q A) (π : Policy Q A)
    (u : Q → ℝ) : ∃ M : Member B, ∀ (M' : Member B) p, VIpol M'.1 π u p ≤ VIpol M.1 π u p := by
  have h := fun p α => bpm66S_max B p α u
  choose F hF hmax using h
  refine ⟨bpm66Mk B F hF, fun M' p => ?_⟩
  rw [bpm66_VIpol_mem, bpm66_VIpol_mem]
  have := hmax p (π p) _ (bpm66_row_mem M' p (π p))
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left this B.γ_nonneg)

open BoundedParamMDP.Optimal BoundedParamMDP.IntervalEval in
theorem bpm66_IVIhi_eq {Q A : Type*} [Fintype Q] (B : BMDP Q A) (π : Policy Q A)
    (u : Q → ℝ) (M : Member B) (hM : ∀ (M' : Member B) p, VIpol M'.1 π u p ≤ VIpol M.1 π u p)
    (p : Q) : IVIhi B π u p = VIpol M.1 π u p := by
  unfold IVIhi
  haveI : Nonempty (Member B) := ⟨M⟩
  apply le_antisymm
  · exact ciSup_le fun M' => hM M' p
  · have hb : BddAbove (Set.range fun M' : Member B => VIpol M'.1 π u p) := by
      refine ⟨VIpol M.1 π u p, ?_⟩
      rintro _ ⟨M', rfl⟩
      exact hM M' p
    exact le_ciSup hb M

open BoundedParamMDP.Optimal BoundedParamMDP.IntervalEval in
theorem bpm66_hi_ge {Q A : Type*} [Fintype Q] (B : BMDP Q A) (π : Policy Q A)
    (u : Q → ℝ) (M' : Member B) (p : Q) : VIpol M'.1 π u p ≤ IVIhi B π u p := by
  obtain ⟨M, hM⟩ := bpm66_attain_hi B π u
  rw [bpm66_IVIhi_eq B π u M hM p]
  exact hM M' p

open BoundedParamMDP.Optimal BoundedParamMDP.IntervalEval in
theorem bpm66_hi_mono {Q A : Type*} [Fintype Q] (B : BMDP Q A) (π : Policy Q A)
    {u v : Q → ℝ} (huv : u ≤ v) : IVIhi B π u ≤ IVIhi B π v := by
  intro p
  obtain ⟨Mu, hMu⟩ := bpm66_attain_hi B π u
  obtain ⟨Mv, hMv⟩ := bpm66_attain_hi B π v
  rw [bpm66_IVIhi_eq B π u Mu hMu p, bpm66_IVIhi_eq B π v Mv hMv p]
  exact le_trans (bpm66_VIpol_mono Mu.1 π huv p) (hMv Mu p)

open BoundedParamMDP.Optimal BoundedParamMDP.IntervalEval in
theorem bpm66_hi_contr {Q A : Type*} [Fintype Q] (B : BMDP Q A) (π : Policy Q A) :
    ContractingWith (Real.toNNReal B.γ) (IVIhi B π) := by
  refine ⟨Real.toNNReal_lt_one.2 B.γ_lt_one, LipschitzWith.of_dist_le_mul fun u v => ?_⟩
  rw [Real.coe_toNNReal _ B.γ_nonneg]
  refine (dist_pi_le_iff (mul_nonneg B.γ_nonneg dist_nonneg)).2 fun p => ?_
  obtain ⟨Mu, hMu⟩ := bpm66_attain_hi B π u
  obtain ⟨Mv, hMv⟩ := bpm66_attain_hi B π v
  rw [Real.dist_eq, bpm66_IVIhi_eq B π u Mu hMu p, bpm66_IVIhi_eq B π v Mv hMv p, abs_le]
  have h1 := hMu Mv p
  have h2 := hMv Mu p
  have h3 := abs_le.1 (bpm66_VIpol_lip Mu.1 π u v p)
  have h4 := abs_le.1 (bpm66_VIpol_lip Mv.1 π u v p)
  rw [Mu.2.2.1] at h3
  rw [Mv.2.2.1] at h4
  constructor <;> linarith [h3.1, h3.2, h4.1, h4.2]

open BoundedParamMDP.Optimal BoundedParamMDP.IntervalEval in
theorem bpm66_upper {Q A : Type*} [Fintype Q] [DecidableEq Q] (B : BMDP Q A)
    (π : Policy Q A) (V₀ : Q → ℝ) :
    Filter.Tendsto (fun n : ℕ => (IVIhi B π)^[n] V₀) Filter.atTop (nhds (upperV B π)) := by
  have hc := bpm66_hi_contr B π
  obtain ⟨U, hfix, hT⟩ : ∃ U, IVIhi B π U = U ∧
      ∀ x, Filter.Tendsto (fun n : ℕ => (IVIhi B π)^[n] x) Filter.atTop (nhds U) :=
    ⟨_, ContractingWith.fixedPoint_isFixedPt hc,
      fun x => ContractingWith.tendsto_iterate_fixedPoint hc x⟩
  obtain ⟨Ms, hMs⟩ := bpm66_attain_hi B π U
  have hVs : VIpol Ms.1 π U = U := by
    funext p
    rw [← bpm66_IVIhi_eq B π U Ms hMs p, hfix]
  have hUval : U = value Ms.1 π := bpm66_fix_unique Ms.1 π U hVs
  have hge : ∀ M : Member B, value M.1 π ≤ U := by
    intro M
    have h1 : value M.1 π ≤ IVIhi B π (value M.1 π) := fun p => by
      have := bpm66_hi_ge B π (value M.1 π) M p
      rwa [bpm66_value_fix] at this
    have h2 : ∀ n : ℕ, value M.1 π ≤ (IVIhi B π)^[n] (value M.1 π) := by
      intro n
      induction n with
      | zero => exact le_rfl
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact le_trans h1 (bpm66_hi_mono B π ih)
    exact ge_of_tendsto' (hT (value M.1 π)) h2
  have hup : upperV B π = U := by
    funext q
    haveI : Nonempty (Member B) := ⟨Ms⟩
    unfold upperV
    apply le_antisymm
    · exact ciSup_le fun M => hge M q
    · have hb : BddAbove (Set.range fun M : Member B => value M.1 π q) := by
        refine ⟨U q, ?_⟩
        rintro _ ⟨M, rfl⟩
        exact hge M q
      refine le_trans ?_ (le_ciSup hb Ms)
      rw [hUval]
  rw [hup]
  exact hT V₀

open BoundedParamMDP.IntervalEval in
theorem solution {Q A : Type*} [Fintype Q] [DecidableEq Q]
    [Fintype A] [Nonempty A] (B : BoundedParamMDP.Optimal.BMDP Q A) (π : BoundedParamMDP.Optimal.Policy Q A)
    (V₀ : (Q → ℝ) × (Q → ℝ)) (hV₀ : V₀.1 ≤ V₀.2) :
    Filter.Tendsto (fun n : ℕ => (IVI B π)^[n] V₀) Filter.atTop
      (nhds (BoundedParamMDP.Optimal.lowerV B π, BoundedParamMDP.Optimal.upperV B π)) := by
  have hit : ∀ n : ℕ, (IVI B π)^[n] V₀ = ((IVIlo B π)^[n] V₀.1, (IVIhi B π)^[n] V₀.2) := by
    intro n
    have hIVI : IVI B π = Prod.map (IVIlo B π) (IVIhi B π) := rfl
    rw [hIVI, Prod.map_iterate]
    rfl
  simp_rw [hit]
  exact (bpm66_lower B π V₀.1).prodMk_nhds (bpm66_upper B π V₀.2)
