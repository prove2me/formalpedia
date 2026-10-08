-- Prove2me | solution 1 for DenardoDP.NStage.theorem4_abc
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:35:26.955963+00:00
-- url     : https://prove2.me/submissions/77349349-ed61-4e3b-9bbd-a2017a619981

import Theorems.Thm_DenardoDP_NStage_sup_modulus_le
import Theorems.Thm_DenardoDP_NStage_lemma1

set_option autoImplicit false
set_option maxHeartbeats 1600000

open DenardoDP.Contraction DenardoDP.NStage Function Filter
open scoped Topology

namespace NStageProof

variable {Ω : Type*}

theorem coord_dist (u v : BFun Ω) (x : Ω) : |u x - v x| ≤ dist u v := by
  simpa [dist_eq_norm, Real.norm_eq_abs] using
    (lp.norm_apply_le_norm ENNReal.top_ne_zero (u - v) x)

theorem dist_bound {u v : BFun Ω} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ x, |u x - v x| ≤ C) : dist u v ≤ C := by
  rw [dist_eq_norm]
  exact lp.norm_le_of_forall_le hC (by simpa [Real.norm_eq_abs] using h)

theorem ple_antisymm {u v : BFun Ω} (huv : PLe u v) (hvu : PLe v u) : u = v := by
  ext x
  exact le_antisymm (huv x) (hvu x)

theorem ple_trans {u v w : BFun Ω} (huv : PLe u v) (hvw : PLe v w) : PLe u w :=
  fun x => le_trans (huv x) (hvw x)

noncomputable def shift (u : BFun Ω) (t : ℝ) : BFun Ω :=
  ⟨fun x => u x + t, memℓp_infty ⟨‖u‖ + |t|, by
    rintro _ ⟨x, rfl⟩
    exact (norm_add_le _ _).trans (add_le_add
      (lp.norm_apply_le_norm ENNReal.top_ne_zero u x) (by simp))⟩⟩

theorem shift_apply (u : BFun Ω) (t : ℝ) (x : Ω) : shift u t x = u x + t := rfl

theorem dist_shift (u : BFun Ω) (t : ℝ) : dist (shift u t) u ≤ |t| := by
  apply dist_bound (abs_nonneg _)
  intro x
  simp [shift_apply]

noncomputable def pmax (u v : BFun Ω) : BFun Ω :=
  ⟨fun x => max (u x) (v x), memℓp_infty ⟨‖u‖ + ‖v‖, by
    rintro _ ⟨x, rfl⟩
    change ‖max (u x) (v x)‖ ≤ ‖u‖ + ‖v‖
    rcases le_total (u x) (v x) with h | h
    · rw [max_eq_right h]
      exact (lp.norm_apply_le_norm ENNReal.top_ne_zero v x).trans
        (le_add_of_nonneg_left (norm_nonneg _))
    · rw [max_eq_left h]
      exact (lp.norm_apply_le_norm ENNReal.top_ne_zero u x).trans
        (le_add_of_nonneg_right (norm_nonneg _))⟩⟩

theorem pmax_apply (u v : BFun Ω) (x : Ω) : pmax u v x = max (u x) (v x) := rfl

theorem family_lub {I : Type*} [Nonempty I] (v : I → BFun Ω) (b : BFun Ω)
    (hb : ∀ i, PLe (v i) b) : ∃ f : BFun Ω, ∀ x, IsLUB (Set.range fun i => v i x) (f x) := by
  classical
  let i₀ : I := Classical.choice inferInstance
  have hlub (x : Ω) : IsLUB (Set.range fun i => v i x) (sSup (Set.range fun i => v i x)) :=
    isLUB_csSup (Set.range_nonempty _) ⟨b x, by rintro _ ⟨i, rfl⟩; exact hb i x⟩
  have hbound (x : Ω) : |sSup (Set.range fun i => v i x)| ≤ ‖v i₀‖ + ‖b‖ := by
    have hlo := (hlub x).1 (Set.mem_range_self i₀)
    have hhi := (hlub x).2 (show b x ∈ upperBounds (Set.range fun i => v i x) from
      by rintro _ ⟨i, rfl⟩; exact hb i x)
    have ha := lp.norm_apply_le_norm ENNReal.top_ne_zero (v i₀) x
    have hc := lp.norm_apply_le_norm ENNReal.top_ne_zero b x
    rw [Real.norm_eq_abs] at ha hc
    rw [abs_le] at ha hc ⊢
    constructor <;> linarith [norm_nonneg (v i₀), norm_nonneg b]
  refine ⟨⟨fun x => sSup (Set.range fun i => v i x), memℓp_infty ?_⟩, ?_⟩
  · refine ⟨‖v i₀‖ + ‖b‖, ?_⟩
    rintro _ ⟨x, rfl⟩
    simpa [Real.norm_eq_abs] using hbound x
  · exact hlub

theorem contracting {B : BFun Ω → BFun Ω} {c : ℝ}
    (hc : c < 1) (hB : ModulusLE B c) : ContractingWith (Real.toNNReal c) B := by
  constructor
  · exact Real.toNNReal_lt_one.mpr hc
  · apply LipschitzWith.of_dist_le_mul
    intro u v
    exact (hB u v).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) dist_nonneg)

theorem unique_fixed {B : BFun Ω → BFun Ω} {c : ℝ}
    (hc : c < 1) (hB : ModulusLE B c) {u v : BFun Ω}
    (hu : B u = u) (hv : B v = v) : u = v := by
  exact (contracting hc hB).fixedPoint_unique' hu hv

theorem iterate_mono {B : BFun Ω → BFun Ω}
    (hB : ∀ u v, PLe u v → PLe (B u) (B v))
    {u v : BFun Ω} (huv : PLe u v) (n : ℕ) : PLe (B^[n] u) (B^[n] v) := by
  induction n with
  | zero => exact huv
  | succ n ih => simpa only [iterate_succ_apply'] using hB _ _ ih

theorem iterate_le {B : BFun Ω → BFun Ω}
    (hB : ∀ u v, PLe u v → PLe (B u) (B v))
    {u : BFun Ω} (hu : PLe (B u) u) (n : ℕ) : PLe (B^[n] u) u := by
  induction n with
  | zero => exact fun _ => le_rfl
  | succ n ih =>
    simpa only [iterate_succ_apply'] using ple_trans (hB _ _ ih) hu

theorem le_iterate {B : BFun Ω → BFun Ω}
    (hB : ∀ u v, PLe u v → PLe (B u) (B v))
    {u : BFun Ω} (hu : PLe u (B u)) (n : ℕ) : PLe u (B^[n] u) := by
  induction n with
  | zero => exact fun _ => le_rfl
  | succ n ih =>
    simpa only [iterate_succ_apply'] using ple_trans hu (hB _ _ ih)

theorem fixed_le {B : BFun Ω → BFun Ω} {c : ℝ}
    (hc : c < 1) (hB : ModulusLE B c)
    (hmono : ∀ u v, PLe u v → PLe (B u) (B v))
    {p w : BFun Ω} (hp : B p = p) (hw : PLe (B w) w) : PLe p w := by
  have hC := contracting hc hB
  have hconv := hC.tendsto_iterate_fixedPoint w
  rw [← hC.fixedPoint_unique hp] at hconv
  intro x
  have heval := (lp.evalCLM ℝ (fun _ : Ω => ℝ) ⊤ x).continuous.tendsto p
  exact le_of_tendsto (heval.comp hconv) (Filter.Eventually.of_forall fun n => iterate_le hmono hw n x)

theorem le_fixed {B : BFun Ω → BFun Ω} {c : ℝ}
    (hc : c < 1) (hB : ModulusLE B c)
    (hmono : ∀ u v, PLe u v → PLe (B u) (B v))
    {p w : BFun Ω} (hp : B p = p) (hw : PLe w (B w)) : PLe w p := by
  have hC := contracting hc hB
  have hconv := hC.tendsto_iterate_fixedPoint w
  rw [← hC.fixedPoint_unique hp] at hconv
  intro x
  have heval := (lp.evalCLM ℝ (fun _ : Ω => ℝ) ⊤ x).continuous.tendsto p
  exact ge_of_tendsto (heval.comp hconv) (Filter.Eventually.of_forall fun n => le_iterate hmono hw n x)

variable {D : Ω → Type*}
variable (h : (x : Ω) → D x → BFun Ω → ℝ)
variable (H : ((x : Ω) → D x) → BFun Ω → BFun Ω)
variable (A : BFun Ω → BFun Ω)

theorem decisions_nonempty (hA : IsMaxOperator h A) : ∀ x, Nonempty (D x) := by
  intro x
  by_contra hc
  rw [not_nonempty_iff] at hc
  have hl := hA 0 x
  have hr : (Set.range fun d : D x => h x d 0) = ∅ := Set.range_eq_empty _
  rw [hr] at hl
  have := hl.2 (show (A 0 x - 1) ∈ upperBounds (∅ : Set ℝ) by simp)
  linarith

theorem H_le_A (hH : IsPolicyOperator h H) (hA : IsMaxOperator h A)
    (δ : (x : Ω) → D x) (w : BFun Ω) : PLe (H δ w) (A w) := by
  intro x
  rw [hH]
  exact (hA w x).1 (Set.mem_range_self (δ x))

theorem H_iterate_le_A (hH : IsPolicyOperator h H) (hA : IsMaxOperator h A)
    (hmono : MonotonicityAssumption H) (δ : (x : Ω) → D x) (w : BFun Ω)
    (n : ℕ) : PLe ((H δ)^[n] w) (A^[n] w) := by
  induction n with
  | zero => exact fun _ => le_rfl
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact ple_trans (hmono δ _ _ ih) (H_le_A h H A hH hA δ _)

theorem policy_fixed (v : ((x : Ω) → D x) → BFun Ω) (N : ℕ) (c : ℝ)
    (hN : NStageContractionAssumption H N c) (hv : ∀ δ, (H δ)^[N] (v δ) = v δ) :
    ∀ δ, H δ (v δ) = v δ ∧ ∀ w, H δ w = w → w = v δ := by
  intro δ
  have hC := contracting hN.2.1 (hN.2.2.1 δ)
  have hp := hC.fixedPoint_unique (hv δ)
  constructor
  · rw [hp]
    exact hC.isFixedPt_fixedPoint_iterate
  · intro w hw
    exact hC.fixedPoint_unique' ((show IsFixedPt (H δ) w from hw).iterate N) (hv δ)

theorem iterate_residual {B : BFun Ω → BFun Ω} (hB : ModulusLE B 1)
    (w : BFun Ω) (n : ℕ) : dist (B^[n] w) w ≤ dist (B w) w * n := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      dist (B^[n+1] w) w ≤ dist (B (B^[n] w)) (B w) + dist (B w) w := by
        rw [iterate_succ_apply']; exact dist_triangle _ _ _
      _ ≤ dist (B^[n] w) w + dist (B w) w := by
        gcongr; simpa using hB (B^[n] w) w
      _ ≤ dist (B w) w * ↑(n+1) := by push_cast; nlinarith

theorem residual_bound (v : ((x : Ω) → D x) → BFun Ω) (N : ℕ) (c : ℝ)
    (hN : NStageContractionAssumption H N c) (hv : ∀ δ, (H δ)^[N] (v δ) = v δ) :
    ∀ δ w, dist (v δ) w ≤ dist (H δ w) w * N / (1-c) := by
  intro δ w
  have hmod := hN.2.2.1 δ (v δ) w
  rw [hv δ] at hmod
  have hres := iterate_residual (hN.2.2.2 δ) w N
  have htri := dist_triangle (v δ) ((H δ)^[N] w) w
  apply (le_div_iff₀ (sub_pos.mpr hN.2.1)).mpr
  nlinarith

theorem abc (v : ((x : Ω) → D x) → BFun Ω) (N : ℕ) (c : ℝ)
    (hH : IsPolicyOperator h H) (hA : IsMaxOperator h A)
    (hmono : MonotonicityAssumption H) (hN : NStageContractionAssumption H N c)
    (hv : ∀ δ, (H δ)^[N] (v δ) = v δ) :
    (∀ δ, H δ (v δ) = v δ ∧ ∀ w, H δ w = w → w = v δ) ∧
    (∀ δ w, dist (v δ) w ≤ dist (H δ w) w * N / (1-c)) ∧
    (∃ E : BFun Ω → BFun Ω, IsNStageSupOperator H N E ∧ ModulusLE E c) ∧
    (∃ f : BFun Ω, IsOptimalReturn v f) := by
  classical
  letI : Nonempty ((x : Ω) → D x) := ⟨fun x => Classical.choice (decisions_nonempty h A hA x)⟩
  have hex (w : BFun Ω) : ∃ e : BFun Ω, ∀ x,
      IsLUB (Set.range fun δ => (H δ)^[N] w x) (e x) :=
    family_lub (fun δ => (H δ)^[N] w) (A^[N] w) (fun δ => H_iterate_le_A h H A hH hA hmono δ w N)
  choose E hE using hex
  have hEc : ModulusLE E c := sup_modulus_le (fun δ => (H δ)^[N]) E c hN.2.2.1 hE
  have hC := contracting hN.2.1 hEc
  let p := hC.fixedPoint E
  have hp : E p = p := hC.fixedPoint_isFixedPt
  have hvp : ∀ δ, PLe (v δ) p := by
    intro δ
    apply fixed_le hN.2.1 (hN.2.2.1 δ)
      (fun u w huw => iterate_mono (fun u w huw => hmono δ w u huw) huw N) (hv δ)
    intro x
    calc
      (H δ)^[N] p x ≤ E p x := (hE p x).1 (Set.mem_range_self δ)
      _ = p x := congrArg (fun z : BFun Ω => z x) hp
  exact ⟨policy_fixed H v N c hN hv, residual_bound H v N c hN hv,
    ⟨E, hE, hEc⟩, family_lub v p hvp⟩

end NStageProof

theorem solution {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → DenardoDP.Contraction.BFun Ω → ℝ) (H : ((x : Ω) → D x) → DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω)
    (A : DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω) (v : ((x : Ω) → D x) → DenardoDP.Contraction.BFun Ω) (N : ℕ) (c : ℝ)
    (hH : DenardoDP.Contraction.IsPolicyOperator h H) (hA : DenardoDP.Contraction.IsMaxOperator h A)
    (hmono : DenardoDP.Contraction.MonotonicityAssumption H) (hN : NStageContractionAssumption H N c)
    (hv : ∀ δ, (H δ)^[N] (v δ) = v δ) :
    (∀ δ, H δ (v δ) = v δ ∧ ∀ w, H δ w = w → w = v δ) ∧
    (∀ δ w, dist (v δ) w ≤ dist (H δ w) w * N / (1 - c)) ∧
    (∃ E : DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω, IsNStageSupOperator H N E ∧ DenardoDP.Contraction.ModulusLE E c) ∧
    (∃ f : DenardoDP.Contraction.BFun Ω, DenardoDP.Contraction.IsOptimalReturn v f) := by
  exact NStageProof.abc h H A v N c hH hA hmono hN hv

#print axioms solution
