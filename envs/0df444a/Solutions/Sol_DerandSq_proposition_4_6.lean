-- Prove2me | solution 1 for DerandSq.proposition_4_6
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:31:28.356756+00:00
-- url     : https://prove2.me/submissions/b3f49062-cf07-48b3-93a5-89031190801d

import Mathlib
import Definitions.Def_DerandSq_tauRed
import Definitions.Def_DerandSq_QH
import Theorems.Thm_DerandSq_lemma_2_2
import Definitions.Def_DerandSq_dsTree
import Definitions.Def_DerandSq_closedWalks

section
set_option autoImplicit false

namespace DerandSq.Dev.P46a

open scoped InnerProductSpace ComplexOrder

/-- Precomposition by an equivalence. -/
noncomputable def compOp {Γ : Type*} (e : Γ ≃ Γ) : L2 Γ →L[ℂ] L2 Γ :=
  LinearMap.mkContinuous
    { toFun := fun f => ⟨fun h => f (e h), by
        have hf := (lp.memℓp f)
        rw [memℓp_gen_iff (by norm_num)] at hf
        show Memℓp (fun h : Γ => f (e h)) 2
        rw [memℓp_gen_iff (by norm_num)]
        exact e.summable_iff.mpr hf⟩
      map_add' := fun f f' => by ext h; rfl
      map_smul' := fun c f => by ext h; rfl }
    1
    (by
      intro f
      rw [one_mul]
      apply le_of_eq
      simp only [LinearMap.coe_mk, AddHom.coe_mk]
      rw [lp.norm_eq_tsum_rpow (by norm_num), lp.norm_eq_tsum_rpow (by norm_num)]
      congr 1
      exact e.tsum_eq (fun h => ‖f h‖ ^ (2 : ENNReal).toReal))

theorem compOp_apply {Γ : Type*} (e : Γ ≃ Γ) (f : L2 Γ) (h : Γ) : compOp e f h = f (e h) := rfl

theorem leftReg_eq {Γ : Type*} [Group Γ] (g : Γ) : leftReg g = compOp (Equiv.mulLeft g⁻¹) :=
  ContinuousLinearMap.ext fun f => lp.ext (funext fun h => rfl)

theorem star_compOp {Γ : Type*} (e : Γ ≃ Γ) : star (compOp e) = compOp e.symm := by
  rw [ContinuousLinearMap.star_eq_adjoint, eq_comm, ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  simp only [lp.inner_eq_tsum, compOp_apply]
  have := e.symm.tsum_eq (fun i => ⟪x i, y (e i)⟫_ℂ)
  simpa using this

open Classical in
theorem delta_apply {Γ : Type*} (g x : Γ) : delta g x = if x = g then 1 else 0 := by
  classical
  simp [delta, lp.single_apply, Pi.single_apply]

/-- The right regular operators `ρ(g) f = f(· g)`. -/
noncomputable def rreg {Γ : Type*} [Group Γ] (g : Γ) : L2 Γ →L[ℂ] L2 Γ :=
  compOp (Equiv.mulRight g)

theorem rreg_apply {Γ : Type*} [Group Γ] (g : Γ) (f : L2 Γ) (x : Γ) : rreg g f x = f (x * g) :=
  rfl

/-- The commutant of the right regular representation. -/
noncomputable abbrev Cm (Γ : Type*) [Group Γ] : StarSubalgebra ℂ (L2 Γ →L[ℂ] L2 Γ) :=
  StarSubalgebra.centralizer ℂ (Set.range (rreg (Γ := Γ)))

instance cmClosed (Γ : Type*) [Group Γ] : IsClosed ((Cm Γ : StarSubalgebra ℂ (L2 Γ →L[ℂ] L2 Γ)) :
    Set (L2 Γ →L[ℂ] L2 Γ)) := by
  rw [StarSubalgebra.coe_centralizer]
  exact Set.isClosed_centralizer _

theorem mem_Cm {Γ : Type*} [Group Γ] (a : L2 Γ →L[ℂ] L2 Γ) :
    a ∈ Cm Γ ↔ ∀ g : Γ, rreg g * a = a * rreg g ∧ star (rreg g) * a = a * star (rreg g) := by
  rw [StarSubalgebra.mem_centralizer_iff]
  simp

theorem delta_eq_rreg {Γ : Type*} [Group Γ] (g : Γ) : delta g = rreg g⁻¹ (delta 1) := by
  ext x
  rw [rreg_apply, delta_apply, delta_apply]
  by_cases h : x = g
  · subst h; simp
  · have : x * g⁻¹ ≠ 1 := fun h' => h (mul_inv_eq_one.1 h')
    rw [if_neg h, if_neg this]

theorem apply_delta {Γ : Type*} [Group Γ] {a : L2 Γ →L[ℂ] L2 Γ} (ha : a ∈ Cm Γ) (g x : Γ) :
    a (delta g) x = a (delta 1) (x * g⁻¹) := by
  have h := congrArg (fun T => T (delta 1)) ((mem_Cm a).1 ha g⁻¹).1
  simp only [ContinuousLinearMap.mul_apply] at h
  rw [delta_eq_rreg g, ← h, rreg_apply]

theorem inner_delta_left {Γ : Type*} [Group Γ] (g : Γ) (f : L2 Γ) :
    ⟪delta g, f⟫_ℂ = f g := by
  classical
  simp [delta, lp.inner_single_left]

theorem inner_delta_right {Γ : Type*} [Group Γ] (g : Γ) (f : L2 Γ) :
    ⟪f, delta g⟫_ℂ = star (f g) := by
  classical
  simp [delta, lp.inner_single_right]

theorem tauRed_eq {Γ : Type*} [Group Γ] (a : L2 Γ →L[ℂ] L2 Γ) : tauRed a = a (delta 1) 1 := by
  rw [tauRed, inner_delta_left]

theorem tauRed_mul {Γ : Type*} [Group Γ] {a b : L2 Γ →L[ℂ] L2 Γ} (ha : a ∈ Cm Γ) :
    tauRed (a * b) = ∑' g : Γ, b (delta 1) g * a (delta 1) g⁻¹ := by
  rw [tauRed, ContinuousLinearMap.mul_apply, ← ContinuousLinearMap.adjoint_inner_left,
    lp.inner_eq_tsum]
  refine tsum_congr fun g => ?_
  have h1 : (ContinuousLinearMap.adjoint a) (delta 1) g = star (a (delta 1) g⁻¹) := by
    rw [← inner_delta_left g, ContinuousLinearMap.adjoint_inner_right, inner_delta_right,
      apply_delta ha]
    simp
  rw [h1]
  simp [mul_comm]

theorem tauRed_star_mul {Γ : Type*} [Group Γ] (a : L2 Γ →L[ℂ] L2 Γ) :
    tauRed (star a * a) = ((‖a (delta 1)‖ ^ 2 : ℝ) : ℂ) := by
  rw [tauRed, ContinuousLinearMap.mul_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  simp

noncomputable def tauL (Γ : Type*) [Group Γ] : Cm Γ →ₗ[ℂ] ℂ where
  toFun a := tauRed (a : L2 Γ →L[ℂ] L2 Γ)
  map_add' a b := by simp [tauRed, inner_add_right]
  map_smul' c a := by simp [tauRed, inner_smul_right]

theorem tauL_apply {Γ : Type*} [Group Γ] (a : Cm Γ) : tauL Γ a = tauRed (a : L2 Γ →L[ℂ] L2 Γ) :=
  rfl

theorem tauL_one {Γ : Type*} [Group Γ] : tauL Γ 1 = 1 := by
  rw [tauL_apply]
  have : ((1 : Cm Γ) : L2 Γ →L[ℂ] L2 Γ) = 1 := rfl
  rw [this, tauRed, ContinuousLinearMap.one_apply, inner_delta_left, delta_apply]
  simp

theorem tauL_trace {Γ : Type*} [Group Γ] (a b : Cm Γ) : tauL Γ (a * b) = tauL Γ (b * a) := by
  rw [tauL_apply, tauL_apply]
  have e1 : ((a * b : Cm Γ) : L2 Γ →L[ℂ] L2 Γ) = (a : L2 Γ →L[ℂ] L2 Γ) * b := rfl
  have e2 : ((b * a : Cm Γ) : L2 Γ →L[ℂ] L2 Γ) = (b : L2 Γ →L[ℂ] L2 Γ) * a := rfl
  rw [e1, e2, tauRed_mul a.2, tauRed_mul b.2]
  rw [← (Equiv.inv Γ).tsum_eq]
  refine tsum_congr fun g => ?_
  simp [mul_comm]

theorem tauL_pos {Γ : Type*} [Group Γ] (a : Cm Γ) : 0 ≤ tauL Γ (star a * a) := by
  rw [tauL_apply]
  have e1 : ((star a * a : Cm Γ) : L2 Γ →L[ℂ] L2 Γ) = star (a : L2 Γ →L[ℂ] L2 Γ) * a := rfl
  rw [e1, tauRed_star_mul]
  exact Complex.zero_le_real.2 (sq_nonneg _)

theorem tauL_faith {Γ : Type*} [Group Γ] (a : Cm Γ) (h : tauL Γ (star a * a) = 0) : a = 0 := by
  rw [tauL_apply] at h
  have e1 : ((star a * a : Cm Γ) : L2 Γ →L[ℂ] L2 Γ) = star (a : L2 Γ →L[ℂ] L2 Γ) * a := rfl
  rw [e1, tauRed_star_mul] at h
  have h0 : (a : L2 Γ →L[ℂ] L2 Γ) (delta 1) = 0 := by
    have : ‖(a : L2 Γ →L[ℂ] L2 Γ) (delta 1)‖ ^ 2 = 0 := by exact_mod_cast h
    exact norm_eq_zero.1 (pow_eq_zero_iff (by norm_num) |>.1 this)
  have h1 : ∀ g : Γ, (a : L2 Γ →L[ℂ] L2 Γ) (delta g) = 0 := by
    intro g
    ext x
    rw [apply_delta a.2, h0]
    rfl
  have h2 : star (a : L2 Γ →L[ℂ] L2 Γ) = 0 := by
    ext f g
    rw [← inner_delta_left g, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, h1 g]
    simp
  exact Subtype.ext (star_eq_zero.1 h2)

theorem lim_Cm {Γ : Type*} [Group Γ] (a : Cm Γ) :
    Filter.Tendsto (fun k : ℕ =>
      (tauRed ((star (a : L2 Γ →L[ℂ] L2 Γ) * (a : L2 Γ →L[ℂ] L2 Γ)) ^ k)).re ^ ((1 : ℝ) / (2 * k)))
      Filter.atTop (nhds ‖(a : L2 Γ →L[ℂ] L2 Γ)‖) := by
  have := DerandSq.lemma_2_2 (tauL Γ) tauL_one tauL_trace tauL_pos tauL_faith a
  exact this

theorem compOp_comm {Γ : Type*} (e1 e2 : Γ ≃ Γ) (h : ∀ x, e2 (e1 x) = e1 (e2 x)) :
    compOp e1 * compOp e2 = compOp e2 * compOp e1 := by
  refine ContinuousLinearMap.ext fun f => lp.ext (funext fun x => ?_)
  show f (e2 (e1 x)) = f (e1 (e2 x))
  rw [h]

theorem leftReg_mem {Γ : Type*} [Group Γ] (g : Γ) : leftReg g ∈ Cm Γ := by
  rw [mem_Cm]
  intro h
  rw [leftReg_eq]
  constructor
  · exact (compOp_comm _ _ (fun x => by simp [mul_assoc])).symm
  · unfold rreg
    rw [star_compOp]
    exact (compOp_comm _ _ (fun x => by simp [mul_assoc])).symm

theorem QH_mem {d : ℕ} (H : SimpleGraph (Fin d)) : QH H ∈ Cm (Gam d) := by
  classical
  unfold QH
  refine sum_mem fun i _ => sum_mem fun j _ => ?_
  split_ifs
  · exact add_mem (mul_mem (leftReg_mem _) (leftReg_mem _))
      (mul_mem (star_mem (leftReg_mem _)) (star_mem (leftReg_mem _)))
  · exact zero_mem _

theorem QH_star {d : ℕ} (H : SimpleGraph (Fin d)) : star (QH H) = QH H := by
  classical
  unfold QH
  rw [star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [star_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs
  · simp [star_add, star_mul, add_comm]
  · simp

theorem first_conj {d : ℕ} (H : SimpleGraph (Fin d)) :
    Filter.Tendsto (fun p : ℕ => (tauRed (QH H ^ (2 * p))).re ^ ((1 : ℝ) / (2 * p)))
      Filter.atTop (nhds ‖QH H‖) := by
  have := lim_Cm (⟨QH H, QH_mem H⟩ : Cm (Gam d))
  simp only [QH_star, ← pow_two, ← pow_mul] at this
  exact this

end DerandSq.Dev.P46a
end

section
set_option autoImplicit false

namespace DerandSq.Dev.P46b

open scoped InnerProductSpace
open DerandSq.Dev.P46a

/-! ### Free product: homomorphisms out of `Γ_d` -/

theorem mGen_inv {d : ℕ} (i : Fin d) : (mGen i)⁻¹ = mGen i :=
  inv_eq_of_mul_eq_one_right (mGen_mul_self i)

/-- A homomorphism `Z₂ → G` sending the generator to an involution. -/
def z2Hom {G : Type*} [Group G] (s : G) (hs : s * s = 1) : Multiplicative (ZMod 2) →* G where
  toFun x := s ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    have key : ∀ a b : ZMod 2, s ^ (a + b).val = s ^ a.val * s ^ b.val := by
      intro a b
      have v0 : (0 : ZMod 2).val = 0 := rfl
      have v1 : (1 : ZMod 2).val = 1 := rfl
      have v2 : (1 + 1 : ZMod 2).val = 0 := rfl
      have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
      rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;> simp [hs, v0, v1, v2]
    simpa using key (Multiplicative.toAdd x) (Multiplicative.toAdd y)

theorem exists_hom {d : ℕ} {G : Type*} [Group G] (f : Fin d → G) (hf : ∀ i, f i * f i = 1) :
    ∃ φ : Gam d →* G, ∀ i, φ (mGen i) = f i := by
  refine ⟨Monoid.CoprodI.lift (fun i => z2Hom (f i) (hf i)), fun i => ?_⟩
  have v1 : (1 : ZMod 2).val = 1 := rfl
  simp [mGen, Monoid.CoprodI.lift_of, z2Hom, v1]

section Free

variable {d : ℕ}

private def sw1 : Equiv.Perm (Fin 3) := Equiv.swap 0 1
private def sw2 : Equiv.Perm (Fin 3) := Equiv.swap 1 2

private theorem sw1_sq : sw1 * sw1 = 1 := Equiv.swap_mul_self _ _
private theorem sw2_sq : sw2 * sw2 = 1 := Equiv.swap_mul_self _ _
private theorem sw1_ne : sw1 ≠ 1 := by unfold sw1; decide
private theorem sw_ne_comm : sw1 * sw2 ≠ sw2 * sw1 := by unfold sw1 sw2; decide
private theorem sw_ne_one : sw1 * sw2 ≠ sw2 * sw2 := by unfold sw1 sw2; decide

theorem mGen_inj {i j : Fin d} (h : i ≠ j) : mGen i ≠ mGen j := by
  classical
  intro heq
  obtain ⟨φ, hφ⟩ := exists_hom (d := d) (G := Equiv.Perm (Fin 3))
    (fun k => if k = i then sw1 else 1) (fun k => by split_ifs <;> simp [sw1_sq])
  have := congrArg φ heq
  rw [hφ, hφ] at this
  simp [Ne.symm h] at this
  exact sw1_ne this

theorem mGen_mul_ne_one {i j : Fin d} (h : i ≠ j) : mGen i * mGen j ≠ 1 := by
  intro h1
  rw [← mGen_mul_self i] at h1
  exact mGen_inj h.symm (mul_left_cancel h1)

theorem mGen_mul_inj {i j i' j' : Fin d} (h : i ≠ j) (h' : i' ≠ j')
    (heq : mGen i * mGen j = mGen i' * mGen j') : i = i' ∧ j = j' := by
  classical
  have hii : i = i' := by
    by_contra hne
    obtain ⟨φ, hφ⟩ := exists_hom (d := d) (G := Equiv.Perm (Fin 3))
      (fun k => if k = i then sw1 else sw2) (fun k => by split_ifs <;> simp [sw1_sq, sw2_sq])
    have := congrArg φ heq
    rw [map_mul, map_mul, hφ, hφ, hφ, hφ] at this
    simp only [if_pos rfl, if_neg (Ne.symm h), if_neg (Ne.symm hne)] at this
    by_cases hj : j' = i
    · simp only [if_pos hj] at this
      exact sw_ne_comm this
    · simp only [if_neg hj] at this
      exact sw_ne_one this
  subst hii
  exact ⟨rfl, by_contra fun hne => mGen_inj hne (mul_left_cancel heq)⟩

end Free

section Walks

variable {V : Type*} (G : SimpleGraph V)

/-- Number of walks of length `n`. -/
noncomputable def wc (n : ℕ) (x y : V) : ℕ := Nat.card {w : G.Walk x y // w.length = n}

open Classical in
theorem wc_zero (x y : V) : wc G 0 x y = if x = y then 1 else 0 := by
  by_cases h : x = y
  · subst h
    rw [if_pos rfl, wc, Nat.card_eq_one_iff_unique]
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨SimpleGraph.Walk.nil, rfl⟩⟩⟩
    have ha := SimpleGraph.Walk.eq_nil_iff_nil.2 (SimpleGraph.Walk.length_eq_zero_iff.1 a.2)
    have hb := SimpleGraph.Walk.eq_nil_iff_nil.2 (SimpleGraph.Walk.length_eq_zero_iff.1 b.2)
    rw [ha, hb]
  · rw [if_neg h, wc]
    have : IsEmpty {w : G.Walk x y // w.length = 0} :=
      ⟨fun w => h (SimpleGraph.Walk.eq_of_length_eq_zero w.2)⟩
    exact Nat.card_of_isEmpty

theorem wc_succ (hfin : ∀ (u y : V) (n : ℕ), Finite {w : G.Walk u y // w.length = n})
    (x y : V) (n : ℕ) [Fintype (G.neighborSet x)] :
    wc G (n + 1) x y = ∑ u : G.neighborSet x, wc G n u y := by
  have : (Σ u : G.neighborSet x, {p : G.Walk u y // p.length = n}) ≃
      {w : G.Walk x y // w.length = n + 1} :=
    Equiv.ofBijective (fun q => ⟨SimpleGraph.Walk.cons (show G.Adj x q.1 from q.1.2) q.2.1, by simp [q.2.2]⟩) (by
      constructor
      · rintro ⟨⟨u, hu⟩, ⟨p, hp⟩⟩ ⟨⟨u', hu'⟩, ⟨p', hp'⟩⟩ heq
        have h1 : SimpleGraph.Walk.cons (show G.Adj x u from hu) p =
            SimpleGraph.Walk.cons (show G.Adj x u' from hu') p' := congrArg Subtype.val heq
        simp only [SimpleGraph.Walk.cons.injEq] at h1
        obtain ⟨rfl, h2⟩ := h1
        have := eq_of_heq h2
        subst this
        rfl
      · rintro ⟨w, hw⟩
        cases w with
        | nil => simp at hw
        | cons h p => exact ⟨⟨⟨_, h⟩, ⟨p, by simpa using hw⟩⟩, rfl⟩)
  rw [wc, ← Nat.card_congr this, Nat.card_sigma]
  rfl

end Walks

section DS

variable {d : ℕ} (H : SimpleGraph (Fin d))

theorem dsTree_adj_iff (x y : Gam d) :
    (dsTree H).Adj x y ↔ ∃ p : Fin d × Fin d, H.Adj p.1 p.2 ∧ y = x * mGen p.1 * mGen p.2 := by
  constructor
  · rintro ⟨_, i, j, hij, rfl⟩
    exact ⟨(i, j), hij, rfl⟩
  · rintro ⟨⟨i, j⟩, hij, rfl⟩
    refine ⟨?_, i, j, hij, rfl⟩
    intro h
    apply mGen_mul_ne_one (H.ne_of_adj hij)
    have : x * (mGen i * mGen j) = x * 1 := by rw [mul_one, ← mul_assoc]; exact h.symm
    exact mul_left_cancel this

noncomputable def nbrEquiv (x : Gam d) :
    {p : Fin d × Fin d // H.Adj p.1 p.2} ≃ (dsTree H).neighborSet x :=
  Equiv.ofBijective
    (fun p => ⟨x * mGen p.1.1 * mGen p.1.2, (dsTree_adj_iff H _ _).2 ⟨p.1, p.2, rfl⟩⟩)
    (by
      constructor
      · rintro ⟨⟨i, j⟩, hij⟩ ⟨⟨i', j'⟩, hij'⟩ h
        have h1 : x * mGen i * mGen j = x * mGen i' * mGen j' := congrArg Subtype.val h
        rw [mul_assoc, mul_assoc] at h1
        have h2 := mGen_mul_inj (H.ne_of_adj hij) (H.ne_of_adj hij') (mul_left_cancel h1)
        obtain ⟨rfl, rfl⟩ := h2
        rfl
      · rintro ⟨y, hy⟩
        obtain ⟨p, hp, rfl⟩ := (dsTree_adj_iff H _ _).1 hy
        exact ⟨⟨p, hp⟩, rfl⟩)

theorem dsTree_finite (u y : Gam d) (n : ℕ) : Finite {w : (dsTree H).Walk u y // w.length = n} := by
  classical
  have hlf : (dsTree H).LocallyFinite := fun x => by
    haveI : Finite ((dsTree H).neighborSet x) := Finite.of_equiv _ (nbrEquiv H x)
    exact Fintype.ofFinite _
  infer_instance

open Classical in
theorem sum_nbr {M : Type*} [AddCommMonoid M] (x : Gam d) (F : Gam d → M)
    [Fintype ((dsTree H).neighborSet x)] :
    ∑ u : (dsTree H).neighborSet x, F u =
      ∑ p : Fin d × Fin d, if H.Adj p.1 p.2 then F (x * mGen p.1 * mGen p.2) else 0 := by
  classical
  rw [← Fintype.sum_equiv (nbrEquiv H x) (fun p => F (x * mGen p.1.1 * mGen p.1.2))
    (fun u => F u) (fun p => rfl)]
  rw [← Finset.sum_filter, ← Finset.sum_subtype (Finset.univ.filter fun p : Fin d × Fin d => H.Adj p.1 p.2)
    (p := fun p : Fin d × Fin d => H.Adj p.1 p.2) (by simp) (fun p => F (x * mGen p.1 * mGen p.2))]

end DS

section Op

theorem leftReg_delta {Γ : Type*} [Group Γ] (g h : Γ) : leftReg g (delta h) = delta (g * h) := by
  ext x
  rw [leftReg_eq, compOp_apply, delta_apply, delta_apply]
  by_cases hx : x = g * h
  · subst hx
    simp
  · have : (Equiv.mulLeft g⁻¹) x ≠ h := fun h' => hx (by
      simp only [Equiv.coe_mulLeft] at h'
      rw [← h']; simp)
    rw [if_neg hx, if_neg this]

theorem star_leftReg {Γ : Type*} [Group Γ] (g : Γ) : star (leftReg g) = leftReg g⁻¹ := by
  rw [leftReg_eq, star_compOp, leftReg_eq]
  congr 1
  ext x
  simp

open Classical in
theorem QH_delta {d : ℕ} (H : SimpleGraph (Fin d)) (g : Gam d) :
    QH H (delta g) = ∑ p : Fin d × Fin d,
      if H.Adj p.1 p.2 then delta (mGen p.1 * mGen p.2 * g) else 0 := by
  classical
  unfold QH
  simp only [ContinuousLinearMap.sum_apply]
  have key : ∀ i j : Fin d, (if i < j ∧ H.Adj i j then
      leftReg (mGen i) * leftReg (mGen j) + star (leftReg (mGen j)) * star (leftReg (mGen i))
      else (0 : L2 (Gam d) →L[ℂ] L2 (Gam d))) (delta g) =
      if i < j ∧ H.Adj i j then delta (mGen i * mGen j * g) + delta (mGen j * mGen i * g) else 0 := by
    intro i j
    split_ifs
    · simp [leftReg_delta, star_leftReg, mGen_inv, mul_assoc]
    · simp
  simp only [key]
  rw [Fintype.sum_prod_type]
  set f : Fin d → Fin d → L2 (Gam d) := fun i j => delta (mGen i * mGen j * g) with hf
  have e1 : ∀ i j : Fin d, (if i < j ∧ H.Adj i j then delta (mGen i * mGen j * g) +
      delta (mGen j * mGen i * g) else 0) =
      (if i < j ∧ H.Adj i j then f i j else 0) + (if i < j ∧ H.Adj i j then f j i else 0) := by
    intro i j
    split_ifs <;> simp [hf]
  have e2 : ∀ i j : Fin d, (if H.Adj i j then delta (mGen i * mGen j * g) else 0) =
      (if i < j ∧ H.Adj i j then f i j else 0) + (if j < i ∧ H.Adj j i then f i j else 0) := by
    intro i j
    by_cases hij : H.Adj i j
    · have hne := H.ne_of_adj hij
      rcases lt_or_gt_of_ne hne with hlt | hlt
      · simp [hf, hij, hlt, not_lt.2 hlt.le]
      · simp [hf, hij, hij.symm, hlt, not_lt.2 hlt.le]
    · have : ¬ H.Adj j i := fun h => hij h.symm
      simp [hij, this]
  have e3 : ∑ i : Fin d, ∑ j : Fin d, (if j < i ∧ H.Adj j i then f i j else 0) =
      ∑ i : Fin d, ∑ j : Fin d, (if i < j ∧ H.Adj i j then f j i else 0) := by
    rw [Finset.sum_comm]
  simp only [e1, e2, Finset.sum_add_distrib, e3]

end Op

section Main

variable {d : ℕ} (H : SimpleGraph (Fin d))

open Classical in
theorem cnt_eq (n : ℕ) : ∀ g h : Gam d,
    (QH H ^ n) (delta g) h = (wc (dsTree H) n g⁻¹ h⁻¹ : ℂ) := by
  induction n with
  | zero =>
    intro g h
    rw [pow_zero, ContinuousLinearMap.one_apply, delta_apply, wc_zero]
    by_cases hh : h = g
    · subst hh; simp
    · have : g⁻¹ ≠ h⁻¹ := fun h' => hh (inv_injective h').symm
      rw [if_neg hh, if_neg this]; simp
  | succ n ih =>
    intro g h
    have hfin := dsTree_finite H
    let _ : Fintype ((dsTree H).neighborSet g⁻¹) := by
      haveI : Finite ((dsTree H).neighborSet g⁻¹) := Finite.of_equiv _ (nbrEquiv H g⁻¹)
      exact Fintype.ofFinite _
    rw [pow_succ, ContinuousLinearMap.mul_apply, QH_delta, map_sum, lp.coeFn_sum,
      Finset.sum_apply, wc_succ _ hfin, Nat.cast_sum]
    rw [sum_nbr H g⁻¹ (fun u => (wc (dsTree H) n u h⁻¹ : ℂ))]
    refine Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun p => ?_)
    obtain ⟨a, b⟩ := p
    by_cases hab : H.Adj a b
    · have hba : H.Adj b a := hab.symm
      simp only [hab, hba, if_true, Equiv.prodComm_apply, Prod.swap_prod_mk]
      rw [ih]
      congr 3
      simp [mul_assoc, mGen_inv]
    · have hba : ¬ H.Adj b a := fun h' => hab h'.symm
      simp [hab, hba]

theorem tauRed_pow (n : ℕ) : tauRed (QH H ^ n) = (closedWalks (dsTree H) 1 n : ℂ) := by
  rw [tauRed_eq, cnt_eq, inv_one]
  rfl

end Main

end DerandSq.Dev.P46b
end

section
set_option autoImplicit false

namespace DerandSq
open DerandSq.Dev.P46a DerandSq.Dev.P46b in
theorem chk_proposition_4_6 {d k : ℕ} (hd : 3 ≤ d) (hk : 1 ≤ k) (H : SimpleGraph (Fin d))
    [DecidableRel H.Adj] (hH : H.IsRegularOfDegree k) :
    Filter.Tendsto (fun p : ℕ => (tauRed (QH H ^ (2 * p))).re ^ ((1 : ℝ) / (2 * p)))
        Filter.atTop (nhds ‖QH H‖) ∧
      Filter.Tendsto (fun p : ℕ => (closedWalks (dsTree H) 1 (2 * p) : ℝ) ^ ((1 : ℝ) / (2 * p)))
        Filter.atTop (nhds ‖QH H‖) := by
  refine ⟨first_conj H, ?_⟩
  have : (fun p : ℕ => (closedWalks (dsTree H) 1 (2 * p) : ℝ) ^ ((1 : ℝ) / (2 * p))) =
      fun p : ℕ => (tauRed (QH H ^ (2 * p))).re ^ ((1 : ℝ) / (2 * p)) := by
    funext p
    rw [tauRed_pow]
    simp
  rw [this]
  exact first_conj H
end DerandSq
end

theorem solution : type_of% @DerandSq.chk_proposition_4_6 := @DerandSq.chk_proposition_4_6
