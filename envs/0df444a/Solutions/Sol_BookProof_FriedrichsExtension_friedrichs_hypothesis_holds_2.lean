-- Prove2me | solution 2 for BookProof.FriedrichsExtension.friedrichs_hypothesis_holds
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T14:34:09.833325+00:00
-- url     : https://prove2.me/submissions/60c7e541-2282-4841-8a9a-771a65f24e62

import Mathlib
import Definitions.Def_ChapterFriedrichsExtension

set_option autoImplicit false

namespace FCex3138

open scoped ComplexConjugate
open BookProof.FarisLavine BookProof.YangMillsFriedrichs

/-- The ℓ² pairing of finitely supported sequences. -/
noncomputable def ip (x y : ℕ →₀ ℂ) : ℂ := x.sum (fun n a => conj a * y n)

theorem ip_eq (x y : ℕ →₀ ℂ) (s : Finset ℕ) (hx : x.support ⊆ s) :
    ip x y = ∑ n ∈ s, conj (x n) * y n :=
  Finsupp.sum_of_support_subset x hx _ (fun n _ => by simp)

/-- `c₀₀(ℕ, ℂ)`, an incomplete complex inner product space. -/
def V : Type := ℕ →₀ ℂ

noncomputable instance instACG : AddCommGroup V := inferInstanceAs (AddCommGroup (ℕ →₀ ℂ))
noncomputable instance instMod : Module ℂ V := inferInstanceAs (Module ℂ (ℕ →₀ ℂ))

def val (x : V) : ℕ →₀ ℂ := x
def mk (f : ℕ →₀ ℂ) : V := f

theorem val_add (x y : V) : val (x + y) = val x + val y := rfl
theorem val_sub (x y : V) : val (x - y) = val x - val y := rfl
theorem val_smul (r : ℂ) (x : V) : val (r • x) = r • val x := rfl
theorem val_zero : val (0 : V) = 0 := rfl
theorem val_mk (f : ℕ →₀ ℂ) : val (mk f) = f := rfl
theorem val_inj {x y : V} (h : val x = val y) : x = y := h

noncomputable instance instInnerV : Inner ℂ V := ⟨fun x y => ip (val x) (val y)⟩

theorem term_re (z : ℂ) : (conj z * z).re = z.re ^ 2 + z.im ^ 2 := by
  simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]; ring

noncomputable instance instCoreV : InnerProductSpace.Core ℂ V where
  conj_inner_symm x y := by
    show conj (ip (val y) (val x)) = ip (val x) (val y)
    rw [ip_eq _ _ ((val x).support ∪ (val y).support) Finset.subset_union_right,
      ip_eq _ _ ((val x).support ∪ (val y).support) Finset.subset_union_left, map_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp [mul_comm]
  re_inner_nonneg x := by
    show 0 ≤ (ip (val x) (val x)).re
    rw [ip_eq _ _ (val x).support subset_rfl, Complex.re_sum]
    refine Finset.sum_nonneg (fun n _ => ?_)
    rw [term_re]; positivity
  add_left x y z := by
    show ip (val (x + y)) (val z) = ip (val x) (val z) + ip (val y) (val z)
    have hs : (val (x + y)).support ⊆ (val x).support ∪ (val y).support := Finsupp.support_add
    rw [ip_eq _ _ _ hs, ip_eq _ _ ((val x).support ∪ (val y).support) Finset.subset_union_left,
      ip_eq _ _ ((val x).support ∪ (val y).support) Finset.subset_union_right,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [val_add, Finsupp.add_apply, map_add, add_mul]
  smul_left x y r := by
    show ip (val (r • x)) (val y) = conj r * ip (val x) (val y)
    have hs : (val (r • x)).support ⊆ (val x).support := Finsupp.support_smul
    rw [ip_eq _ _ _ hs, ip_eq _ _ (val x).support subset_rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [val_smul, Finsupp.smul_apply, smul_eq_mul, map_mul, mul_assoc]
  definite x hx := by
    have hx' : ip (val x) (val x) = 0 := hx
    rw [ip_eq _ _ (val x).support subset_rfl] at hx'
    have hre := congrArg Complex.re hx'
    rw [Complex.re_sum, Complex.zero_re] at hre
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun n _ => by
      rw [term_re]; positivity)).1 hre
    apply val_inj
    rw [val_zero]
    refine Finsupp.ext fun n => ?_
    by_contra hne
    have hn : n ∈ (val x).support := Finsupp.mem_support_iff.2 (by simpa using hne)
    have h0 := hterm n hn
    rw [term_re] at h0
    have hr : (val x n).re = 0 := by nlinarith [sq_nonneg (val x n).re, sq_nonneg (val x n).im]
    have hi : (val x n).im = 0 := by nlinarith [sq_nonneg (val x n).re, sq_nonneg (val x n).im]
    exact hne (by simpa using Complex.ext hr hi)

noncomputable instance instNormedV : NormedAddCommGroup V :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := instCoreV)

noncomputable instance instIPSV : InnerProductSpace ℂ V := .ofCore _

theorem inner_V (x y : V) : (inner ℂ x y : ℂ) = ip (val x) (val y) := rfl

/-! ## basis vectors and the sum functional -/

noncomputable def e (m : ℕ) : V := mk (Finsupp.single m 1)

theorem val_e (m n : ℕ) : val (e m) n = if m = n then 1 else 0 := by
  simp [e, val_mk, Finsupp.single_apply]

theorem inner_e_left (m : ℕ) (z : V) : (inner ℂ (e m) z : ℂ) = val z m := by
  rw [inner_V]
  unfold ip
  rw [e, val_mk, Finsupp.sum_single_index] <;> simp

theorem inner_e_right (m : ℕ) (z : V) : (inner ℂ z (e m) : ℂ) = conj (val z m) := by
  rw [← inner_conj_symm, inner_e_left]

theorem sum_eq' (f : ℕ →₀ ℂ) (s : Finset ℕ) (h : f.support ⊆ s) :
    f.sum (fun _ a => a) = ∑ n ∈ s, f n :=
  Finsupp.sum_of_support_subset f h _ (fun _ _ => rfl)

noncomputable def phi : V →ₗ[ℂ] ℂ where
  toFun x := (val x).sum (fun _ a => a)
  map_add' x y := by
    have hs : (val (x + y)).support ⊆ (val x).support ∪ (val y).support := Finsupp.support_add
    rw [sum_eq' _ _ hs, sum_eq' (val x) ((val x).support ∪ (val y).support)
      Finset.subset_union_left, sum_eq' (val y) ((val x).support ∪ (val y).support)
      Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [val_add, Finsupp.add_apply]
  map_smul' r x := by
    have hs : (val (r • x)).support ⊆ (val x).support := Finsupp.support_smul
    rw [sum_eq' _ _ hs, sum_eq' (val x) _ subset_rfl, RingHom.id_apply, smul_eq_mul,
      Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [val_smul, Finsupp.smul_apply, smul_eq_mul]

theorem phi_apply (x : V) : phi x = (val x).sum (fun _ a => a) := rfl

theorem phi_e (m : ℕ) : phi (e m) = 1 := by
  rw [phi_apply, e, val_mk, Finsupp.sum_single_index]; rfl

/-! ## the diagonal operator `diag(-1, 4, 16, 64, …)` -/

noncomputable def w (n : ℕ) : ℝ := if n = 0 then -1 else 4 ^ n

noncomputable def Tf (x : ℕ →₀ ℂ) : ℕ →₀ ℂ :=
  Finsupp.ofSupportFinite (fun m => (w m : ℂ) * x m)
    (x.finite_support.subset (fun m hm => by
      simp only [Function.mem_support] at hm ⊢
      exact right_ne_zero_of_mul hm))

theorem Tf_apply (x : ℕ →₀ ℂ) (m : ℕ) : Tf x m = (w m : ℂ) * x m := rfl

theorem Tf_support (x : ℕ →₀ ℂ) : (Tf x).support ⊆ x.support := fun m hm => by
  rw [Finsupp.mem_support_iff] at hm ⊢
  rw [Tf_apply] at hm
  exact right_ne_zero_of_mul hm

noncomputable def T : V →ₗ[ℂ] V where
  toFun x := mk (Tf (val x))
  map_add' x y := val_inj (Finsupp.ext fun m => by
    show Tf (val (x + y)) m = (Tf (val x) + Tf (val y)) m
    rw [Finsupp.add_apply, Tf_apply, Tf_apply, Tf_apply, val_add, Finsupp.add_apply, mul_add])
  map_smul' r x := val_inj (Finsupp.ext fun m => by
    show Tf (val (r • x)) m = (r • Tf (val x)) m
    rw [Finsupp.smul_apply, Tf_apply, Tf_apply, val_smul, Finsupp.smul_apply, smul_eq_mul,
      smul_eq_mul]
    ring)

theorem val_T (x : V) : val (T x) = Tf (val x) := rfl

theorem T_symm (x y : V) : (inner ℂ (T x) y : ℂ) = inner ℂ x (T y) := by
  rw [inner_V, inner_V, val_T, val_T, ip_eq _ _ (val x).support (Tf_support _),
    ip_eq _ _ (val x).support subset_rfl]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Tf_apply, Tf_apply, map_mul, Complex.conj_ofReal]
  ring

/-! ## positivity on the kernel of the sum functional -/

theorem geom_quarter (N : ℕ) : ∑ i ∈ Finset.range N, ((1 : ℝ) / 4) ^ (i + 1) ≤ 1 / 3 := by
  have key : ∀ N : ℕ, ∑ i ∈ Finset.range N, ((1 : ℝ) / 4) ^ (i + 1)
      = 1 / 3 - (1 / 3) * ((1 : ℝ) / 4) ^ N := by
    intro N
    induction N with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ, ih, pow_succ]; ring
  rw [key]
  have : (0 : ℝ) ≤ ((1 : ℝ) / 4) ^ N := by positivity
  linarith

theorem pos_key (f : ℕ →₀ ℂ) (hf : f.sum (fun _ a => a) = 0) : 0 ≤ (ip f (Tf f)).re := by
  set N := f.support.sup id with hN
  have hsub : f.support ⊆ Finset.range (N + 1) := fun n hn => by
    have := Finset.le_sup (f := id) hn
    rw [Finset.mem_range]; simp only [id] at this; omega
  rw [sum_eq' f _ hsub, Finset.sum_range_succ'] at hf
  rw [ip_eq _ _ _ hsub, Finset.sum_range_succ', Complex.add_re, Complex.re_sum]
  have hterm : ∀ (r : ℝ) (z : ℂ), (conj z * ((r : ℂ) * z)).re = r * ‖z‖ ^ 2 := by
    intro r z
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  simp only [Tf_apply, hterm]
  have hw0 : w 0 = -1 := by simp [w]
  have hws : ∀ i : ℕ, w (i + 1) = 4 ^ (i + 1) := fun i => by simp [w]
  simp only [hw0, hws]
  -- f 0 = - Σ f (i+1)
  have h0 : f 0 = -∑ i ∈ Finset.range N, f (i + 1) := by linear_combination hf
  have hn0 : ‖f 0‖ ≤ ∑ i ∈ Finset.range N, ‖f (i + 1)‖ := by
    rw [h0, norm_neg]; exact norm_sum_le _ _
  have hcs : (∑ i ∈ Finset.range N, ‖f (i + 1)‖) ^ 2 ≤
      (∑ i ∈ Finset.range N, ((1 : ℝ) / 4) ^ (i + 1)) *
        ∑ i ∈ Finset.range N, (4 : ℝ) ^ (i + 1) * ‖f (i + 1)‖ ^ 2 := by
    refine Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul _ (fun i _ => by positivity)
      (fun i _ => by positivity) (fun i _ => ?_)
    rw [← mul_assoc, ← mul_pow]; norm_num
  have hg := geom_quarter N
  have hS : 0 ≤ ∑ i ∈ Finset.range N, (4 : ℝ) ^ (i + 1) * ‖f (i + 1)‖ ^ 2 :=
    Finset.sum_nonneg (fun i _ => by positivity)
  have hsq : ‖f 0‖ ^ 2 ≤ (∑ i ∈ Finset.range N, ‖f (i + 1)‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hn0 2
  nlinarith

/-! ## the dense domain -/

noncomputable def D : Submodule ℂ V := LinearMap.ker phi

noncomputable def avg (K : ℕ) : ℕ →₀ ℂ := ∑ m ∈ Finset.range K, Finsupp.single m ((1 : ℂ) / K)

theorem avg_apply (K n : ℕ) : avg K n = if n < K then (1 : ℂ) / K else 0 := by
  simp [avg, Finsupp.finsetSum_apply, Finsupp.single_apply]

theorem avg_support (K : ℕ) : (avg K).support ⊆ Finset.range K := fun n hn => by
  rw [Finsupp.mem_support_iff, avg_apply] at hn
  rw [Finset.mem_range]
  by_contra h
  exact hn (if_neg h)

theorem ip_avg (K : ℕ) (hK : 0 < K) : ip (avg K) (avg K) = 1 / K := by
  rw [ip_eq _ _ _ (avg_support K)]
  rw [Finset.sum_congr rfl (fun n hn => by
    rw [avg_apply, if_pos (Finset.mem_range.1 hn)])]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  simp only [map_div₀, map_one, map_natCast]
  field_simp

theorem phi_avg (K : ℕ) (hK : 0 < K) : phi (mk (avg K)) = 1 := by
  rw [phi_apply, val_mk, sum_eq' _ _ (avg_support K)]
  rw [Finset.sum_congr rfl (fun n hn => by
    rw [avg_apply, if_pos (Finset.mem_range.1 hn)])]
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hK' : (K : ℂ) ≠ 0 := by exact_mod_cast hK.ne'
  field_simp

theorem e0_mem_closure : e 0 ∈ closure (D : Set V) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (pow_pos hε 2)
  refine ⟨e 0 - mk (avg (n + 1)), ?_, ?_⟩
  · show phi (e 0 - mk (avg (n + 1))) = 0
    rw [map_sub, phi_e, phi_avg _ (Nat.succ_pos n), sub_self]
  · rw [dist_eq_norm, sub_sub_cancel]
    have h2 : ‖mk (avg (n + 1))‖ ^ 2 = 1 / ((n : ℝ) + 1) := by
      rw [← BookProof.FriedrichsExtension.re_inner_self, inner_V, val_mk,
        ip_avg _ (Nat.succ_pos n)]
      push_cast
      rw [Complex.div_re]
      simp only [Complex.one_re, Complex.one_im]
      have : Complex.normSq ((n : ℂ) + 1) = ((n : ℝ) + 1) ^ 2 := by
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
          Complex.normSq_ofReal]; ring
      rw [this]
      have hre : ((n : ℂ) + 1).re = (n : ℝ) + 1 := by simp
      rw [hre]
      have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      field_simp
      simp
    have hnn := norm_nonneg (mk (avg (n + 1)))
    nlinarith

theorem D_dense : Dense (D : Set V) := by
  have h0 : e 0 ∈ D.topologicalClosure := by
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]; exact e0_mem_closure
  have htop : D.topologicalClosure = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [← sub_add_cancel x (phi x • e 0)]
    refine add_mem (D.le_topologicalClosure ?_) (Submodule.smul_mem _ _ h0)
    show phi (x - phi x • e 0) = 0
    rw [map_sub, map_smul, phi_e, smul_eq_mul, mul_one, sub_self]
  exact Submodule.dense_iff_topologicalClosure_eq_top.2 htop

/-! ## the refutation -/

theorem pos_D (x : D) : 0 ≤ quadForm (T ∘ₗ D.subtype) x := by
  rw [quadForm, LinearMap.comp_apply, Submodule.subtype_apply, inner_V, val_T]
  exact pos_key _ (LinearMap.mem_ker.1 x.2)

theorem refute (h : ∀ (D' : Submodule ℂ V) (H' : D' →ₗ[ℂ] V), Dense (D' : Set V) →
      SymmetricOn D' H' → (∀ x : D', 0 ≤ quadForm H' x) →
      ∃ (Dom : Submodule ℂ V) (A : Dom →ₗ[ℂ] V), IsPositiveSelfAdjointExtension H' A) :
    False := by
  obtain ⟨Dom, A, h1, h2, h3, h4⟩ := h D (T ∘ₗ D.subtype) D_dense
    (fun x y => T_symm x y) (fun x => pos_D x)
  have hDom : ∀ x : V, phi x = 0 → x ∈ Dom := fun x hx => (h1 ⟨x, hx⟩).1
  have hA : ∀ (x : V) (hx : phi x = 0) (hd : x ∈ Dom), A ⟨x, hd⟩ = T x := fun x hx hd => by
    obtain ⟨_, he⟩ := h1 ⟨x, hx⟩
    exact he
  by_cases he : e 0 ∈ Dom
  · set a := A ⟨e 0, he⟩ with ha
    set m := (val a).support.sup id + 1 with hm
    have ham : val a m = 0 := by
      rw [← Finsupp.notMem_support_iff]
      intro hmem
      have := Finset.le_sup (f := id) hmem
      simp only [id] at this
      omega
    have hm0 : m ≠ 0 := by omega
    have hd : phi (e 0 - e m) = 0 := by rw [map_sub, phi_e, phi_e, sub_self]
    have key := h2 ⟨e 0 - e m, hDom _ hd⟩ ⟨e 0, he⟩
    simp only at key
    rw [hA _ hd, inner_e_right, val_T, Tf_apply, inner_sub_left, inner_e_left, inner_e_left,
      ← ha, ham, val_sub, Finsupp.sub_apply, val_e, val_e, if_pos rfl, if_neg hm0] at key
    have hw0 : w 0 = -1 := by simp [w]
    rw [hw0] at key
    have hval : val a 0 = -1 := by
      have : val a 0 = conj (((-1 : ℝ) : ℂ) * (1 - 0)) := by rw [key]; ring
      rw [this]; simp
    have hp := h3 ⟨e 0, he⟩
    rw [quadForm, ← ha] at hp
    simp only at hp
    rw [inner_e_left, hval] at hp
    norm_num at hp
  · apply he
    obtain ⟨hw, -⟩ := h4 (e 0) (T (e 0)) (fun v => by
      have hv : phi (v : V) = 0 := by
        by_contra hne
        apply he
        have h' : (v : V) - phi v • e 0 ∈ Dom := hDom _ (by
          rw [map_sub, map_smul, phi_e, smul_eq_mul, mul_one, sub_self])
        have h'' : phi v • e 0 ∈ Dom := by
          have := Dom.sub_mem v.2 h'
          rwa [sub_sub_cancel] at this
        have := Dom.smul_mem (phi v)⁻¹ h''
        rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at this
      have hAv : A v = T v := hA _ hv v.2
      rw [hAv]
      exact T_symm _ _)
    exact hw

end FCex3138

open BookProof.FriedrichsExtension BookProof.FarisLavine BookProof.YangMillsFriedrichs BookProof.HashimotoShiftInvert BookProof.HermiteGalerkin in
theorem solution : ¬ (∀ {F : Type} [NormedAddCommGroup F] [InnerProductSpace ℂ F],
    ∀ (D' : Submodule ℂ F) (H' : D' →ₗ[ℂ] F), Dense (D' : Set F) →
      SymmetricOn D' H' → (∀ x : D', 0 ≤ quadForm H' x) →
      ∃ (Dom : Submodule ℂ F) (A : Dom →ₗ[ℂ] F), IsPositiveSelfAdjointExtension H' A) := by
  intro h
  exact FCex3138.refute (fun D' H' hd hs hp => h D' H' hd hs hp)
