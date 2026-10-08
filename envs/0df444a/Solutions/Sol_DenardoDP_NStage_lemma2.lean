-- Prove2me | solution 1 for DenardoDP.NStage.lemma2
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-07T12:35:48.076973+00:00
-- url     : https://prove2.me/submissions/9cc00ddf-abbb-4c8f-a0a0-ab8034bba058

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

theorem approx_policy (hH : IsPolicyOperator h H) (hA : IsMaxOperator h A)
    (w : BFun Ω) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : (x : Ω) → D x, ∀ x, A w x - ε ≤ H δ w x := by
  classical
  have hx (x : Ω) : ∃ d : D x, A w x - ε ≤ h x d w := by
    by_contra! hn
    have hh : A w x ≤ A w x - ε := (hA w x).2 (by
      rintro _ ⟨d, rfl⟩; exact le_of_lt (hn d))
    linarith
  choose δ hδ using hx
  refine ⟨δ, ?_⟩
  intro x
  rw [hH]
  exact hδ x

theorem approx_iterate {B : BFun Ω → BFun Ω}
    (hmono : ∀ u v, PLe u v → PLe (B u) (B v)) (hB : ModulusLE B 1)
    (p : BFun Ω) {ε : ℝ} (hε : 0 ≤ ε) (hp : ∀ x, p x - ε ≤ B p x) :
    ∀ n : ℕ, ∀ x, p x - n * ε ≤ B^[n] p x := by
  intro n
  induction n with
  | zero => simpa using (show ∀ x, p x ≤ p x from fun _ => le_rfl)
  | succ n ih =>
    have hn : 0 ≤ (n : ℝ) * ε := mul_nonneg (Nat.cast_nonneg _) hε
    have hshift : PLe (shift p (-((n:ℝ)*ε))) (B^[n] p) := by
      intro x
      simpa [shift_apply, sub_eq_add_neg] using ih x
    have hdist : dist (B (shift p (-((n:ℝ)*ε)))) (B p) ≤ (n:ℝ)*ε := by
      have h₁ := hB (shift p (-((n:ℝ)*ε))) p
      have h₂ := dist_shift p (-((n:ℝ)*ε))
      simp only [one_mul] at h₁
      simp only [abs_neg, abs_of_nonneg hn] at h₂
      exact h₁.trans h₂
    intro x
    have h₁ := (abs_le.mp ((coord_dist _ _ x).trans hdist)).1
    have h₂ := hmono _ _ hshift x
    have h₃ := hp x
    rw [iterate_succ_apply']
    push_cast
    linarith

theorem lemma_two (v : ((x : Ω) → D x) → BFun Ω) (N : ℕ) (c : ℝ)
    (hH : IsPolicyOperator h H) (hA : IsMaxOperator h A)
    (hmono : MonotonicityAssumption H) (hN : NStageContractionAssumption H N c)
    (hv : ∀ δ, (H δ)^[N] (v δ) = v δ)
    (f : BFun Ω) (hf : IsOptimalReturn v f) :
    ((∀ w, PLe (A w) w → PLe f w) ∧ (∀ w, PLe w (A w) → PLe w f)) ∧
    (∀ δ, PLe (v δ) (A (v δ))) ∧
    (∀ δ w, PLe w (H δ w) → PLe (H δ w) (v δ)) := by
  classical
  have hfix := policy_fixed H v N c hN hv
  have hAm := (DenardoDP.NStage.lemma1 h H A hH hA hmono).1
  have hAf : PLe f (A f) := by
    intro x
    apply (hf x).2
    rintro _ ⟨δ, rfl⟩
    calc
      v δ x = H δ (v δ) x := congrArg (fun z : BFun Ω => z x) (hfix δ).1.symm
      _ ≤ H δ f x := hmono δ f (v δ) (fun y => (hf y).1 (Set.mem_range_self δ)) x
      _ ≤ A f x := H_le_A h H A hH hA δ f x
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro w hw x
    apply (hf x).2
    rintro _ ⟨δ, rfl⟩
    have hHw := ple_trans (H_le_A h H A hH hA δ w) hw
    exact fixed_le hN.2.1 (hN.2.2.1 δ)
      (fun u w huw => iterate_mono (fun u w huw => hmono δ w u huw) huw N)
      (hv δ) (iterate_le (fun u w huw => hmono δ w u huw) hHw N) x
  · intro w hw x
    let u := pmax w f
    have hwu : PLe w u := fun y => le_max_left _ _
    have hfu : PLe f u := fun y => le_max_right _ _
    have hu : PLe u (A u) := by
      intro y
      exact max_le (le_trans (hw y) (hAm u w hwu y)) (le_trans (hAf y) (hAm u f hfu y))
    let p := A u
    apply le_of_forall_pos_le_add
    intro ε hε
    have hNp : (0:ℝ) < N := Nat.cast_pos.mpr hN.1
    have hcp : 0 < 1-c := sub_pos.mpr hN.2.1
    let η := ε * (1-c) / N
    have hη : 0 < η := div_pos (mul_pos hε hcp) hNp
    obtain ⟨δ, hδ⟩ := approx_policy h H A hH hA u hη
    have hδp : ∀ y, p y - η ≤ H δ p y := by
      intro y
      exact (hδ y).trans (hmono δ p u hu y)
    have hvf : PLe (v δ) f := fun y => (hf y).1 (Set.mem_range_self δ)
    have hvp : PLe (v δ) p := ple_trans hvf (ple_trans hfu hu)
    have hiter := approx_iterate (fun u w huw => hmono δ w u huw)
      (hN.2.2.2 δ) p hη.le hδp N
    have hmod := hN.2.2.1 δ p (v δ)
    rw [hv δ] at hmod
    have hnon : 0 ≤ (N:ℝ)*η + c * dist p (v δ) :=
      add_nonneg (mul_nonneg (Nat.cast_nonneg _) hη.le) (dist_nonneg.trans hmod)
    have hb : dist p (v δ) ≤ (N:ℝ)*η + c * dist p (v δ) := by
      apply dist_bound hnon
      intro y
      rw [abs_of_nonneg (sub_nonneg.mpr (hvp y))]
      have hb := (abs_le.mp ((coord_dist _ _ y).trans hmod)).2
      linarith [hiter y]
    have hNη : (N:ℝ)*η = ε*(1-c) := by
      dsimp [η]
      field_simp
    have hd : dist p (v δ) ≤ ε := by
      rw [hNη] at hb
      nlinarith
    have hx := (abs_le.mp ((coord_dist p (v δ) x).trans hd)).2
    have hxw : w x ≤ p x := le_trans (hwu x) (hu x)
    linarith [hvf x]
  · intro δ
    intro x
    calc
      v δ x = H δ (v δ) x := congrArg (fun z : BFun Ω => z x) (hfix δ).1.symm
      _ ≤ A (v δ) x := H_le_A h H A hH hA δ (v δ) x
  · intro δ w hw
    have hwp : PLe w (v δ) := le_fixed hN.2.1 (hN.2.2.1 δ)
      (fun u w huw => iterate_mono (fun u w huw => hmono δ w u huw) huw N)
      (hv δ) (le_iterate (fun u w huw => hmono δ w u huw) hw N)
    intro x
    calc
      H δ w x ≤ H δ (v δ) x := hmono δ (v δ) w hwp x
      _ = v δ x := congrArg (fun z : BFun Ω => z x) (hfix δ).1

end NStageProof

theorem solution {Ω : Type*} {D : Ω → Type*}
    (h : (x : Ω) → D x → DenardoDP.Contraction.BFun Ω → ℝ) (H : ((x : Ω) → D x) → DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω)
    (A : DenardoDP.Contraction.BFun Ω → DenardoDP.Contraction.BFun Ω) (v : ((x : Ω) → D x) → DenardoDP.Contraction.BFun Ω) (N : ℕ) (c : ℝ)
    (hH : DenardoDP.Contraction.IsPolicyOperator h H) (hA : DenardoDP.Contraction.IsMaxOperator h A)
    (hmono : DenardoDP.Contraction.MonotonicityAssumption H) (hN : NStageContractionAssumption H N c)
    (hv : ∀ δ, (H δ)^[N] (v δ) = v δ)
    (f : DenardoDP.Contraction.BFun Ω) (hf : DenardoDP.Contraction.IsOptimalReturn v f) :
    ((∀ w, DenardoDP.Contraction.PLe (A w) w → DenardoDP.Contraction.PLe f w) ∧ (∀ w, DenardoDP.Contraction.PLe w (A w) → DenardoDP.Contraction.PLe w f)) ∧
    (∀ δ, DenardoDP.Contraction.PLe (v δ) (A (v δ))) ∧
    (∀ δ w, DenardoDP.Contraction.PLe w (H δ w) → DenardoDP.Contraction.PLe (H δ w) (v δ)) := by
  exact NStageProof.lemma_two h H A v N c hH hA hmono hN hv f hf

#print axioms solution
