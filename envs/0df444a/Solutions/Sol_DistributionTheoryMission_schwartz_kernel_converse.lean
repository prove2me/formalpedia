-- Prove2me | solution 1 for DistributionTheoryMission.schwartz_kernel_converse
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-24T13:03:45.688422+00:00
-- url     : https://prove2.me/submissions/da82642f-397f-45cb-ba5d-2a7ac4613689

import Definitions.Def_liuyao_ca_fd889115_k1_Distributions_KernelTargets
import Theorems.Thm_DistributionTheoryMission_tensor_tests
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueCongruence
import Mathlib.Algebra.BigOperators.Fin
import Definitions.Def_liuyao_ca_fd889115_k1_Analysis_RealValueArithmetic
open scoped BigOperators
set_option autoImplicit true
open ComputableAnalysis ComputableDistributions
open ComputableAnalysis.RealComputeQuotient

namespace KC
theorem eqv {x y : RealCompute} (hx : x.Valid) (hy : y.Valid)
    (h : RealComputeQuotient.ofRaw x hx = RealComputeQuotient.ofRaw y hy) : x.Equiv y :=
  equiv_of_ofRaw_eq h

theorem mul_add_l {a b c : RealCompute} (ha : a.Valid) (hb : b.Valid) (hc : c.Valid) :
    (RealCompute.mul (RealCompute.add a b) c).Equiv
      (RealCompute.add (RealCompute.mul a c) (RealCompute.mul b c)) := by
  refine eqv (RealCompute.mul_valid (RealCompute.add_valid ha hb) hc)
    (RealCompute.add_valid (RealCompute.mul_valid ha hc) (RealCompute.mul_valid hb hc)) ?_
  exact add_mul (ofRaw a ha) (ofRaw b hb) (ofRaw c hc)

theorem mul_add_r {a b c : RealCompute} (ha : a.Valid) (hb : b.Valid) (hc : c.Valid) :
    (RealCompute.mul a (RealCompute.add b c)).Equiv
      (RealCompute.add (RealCompute.mul a b) (RealCompute.mul a c)) := by
  refine eqv (RealCompute.mul_valid ha (RealCompute.add_valid hb hc))
    (RealCompute.add_valid (RealCompute.mul_valid ha hb) (RealCompute.mul_valid ha hc)) ?_
  exact mul_add (ofRaw a ha) (ofRaw b hb) (ofRaw c hc)

theorem mul_assoc_l {r a c : RealCompute} (hr : r.Valid) (ha : a.Valid) (hc : c.Valid) :
    (RealCompute.mul (RealCompute.mul r a) c).Equiv
      (RealCompute.mul r (RealCompute.mul a c)) := by
  refine eqv (RealCompute.mul_valid (RealCompute.mul_valid hr ha) hc)
    (RealCompute.mul_valid hr (RealCompute.mul_valid ha hc)) ?_
  exact mul_assoc (ofRaw r hr) (ofRaw a ha) (ofRaw c hc)

theorem mul_assoc_r {r a c : RealCompute} (hr : r.Valid) (ha : a.Valid) (hc : c.Valid) :
    (RealCompute.mul a (RealCompute.mul r c)).Equiv
      (RealCompute.mul r (RealCompute.mul a c)) := by
  refine eqv (RealCompute.mul_valid ha (RealCompute.mul_valid hr hc))
    (RealCompute.mul_valid hr (RealCompute.mul_valid ha hc)) ?_
  have h1 : ofRaw a ha * (ofRaw r hr * ofRaw c hc) = ofRaw r hr * (ofRaw a ha * ofRaw c hc) := by
    rw [← mul_assoc, mul_comm (ofRaw a ha) (ofRaw r hr),
      mul_assoc]
  exact h1

theorem zero_mul_l {a : RealCompute} (ha : a.Valid) (z : RealCompute) (hz : z.Equiv (RealCompute.ofRat 0)) (hz' : z.Valid):
    (RealCompute.mul z a).Equiv (RealCompute.ofRat 0) := by
  refine eqv (RealCompute.mul_valid hz' ha) (RealCompute.ofRat_valid 0) ?_
  have : ofRaw z hz' = ofRaw (RealCompute.ofRat 0) (RealCompute.ofRat_valid 0) :=
    ofRaw_eq_ofRaw hz
  change ofRaw z hz' * ofRaw a ha = 0
  rw [this]; exact zero_mul _

theorem mul_zero_r {a : RealCompute} (ha : a.Valid) (z : RealCompute) (hz : z.Equiv (RealCompute.ofRat 0)) (hz' : z.Valid):
    (RealCompute.mul a z).Equiv (RealCompute.ofRat 0) := by
  refine eqv (RealCompute.mul_valid ha hz') (RealCompute.ofRat_valid 0) ?_
  have : ofRaw z hz' = ofRaw (RealCompute.ofRat 0) (RealCompute.ofRat_valid 0) :=
    ofRaw_eq_ofRaw hz
  change ofRaw a ha * ofRaw z hz' = 0
  rw [this]; exact mul_zero _

theorem small_mul {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) {a b : Rat}
    (h1 : RealApproximationOrder.Small (RealApproximationOrder.parameter x hx) a)
    (h2 : RealApproximationOrder.Small (RealApproximationOrder.parameter y hy) b) :
    RealApproximationOrder.Small (RealApproximationOrder.parameter (RealCompute.mul x y)
      (RealCompute.mul_valid hx hy)) (a * b) := by
  have := RealApproximationOrder.Small.mul h1 h2
  exact this

theorem small_congr {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) {a : Rat}
    (h1 : RealApproximationOrder.Small (RealApproximationOrder.parameter x hx) a)
    (he : x.Equiv y) :
    RealApproximationOrder.Small (RealApproximationOrder.parameter y hy) a :=
  RealApproximationOrder.Small.congr h1 he

theorem order_eq_sum : ∀ {d : Nat} (α : MultiIndex d), multiIndexOrder α = ∑ i, α i
  | 0, α => by simp [multiIndexOrder]
  | d + 1, α => by
    rw [Fin.sum_univ_castSucc]
    change multiIndexOrder (fun i : Fin d => α i.castSucc) + α (Fin.last d) = _
    rw [order_eq_sum]

theorem order_castAdd_le {m n : Nat} (α : MultiIndex (m + n)) :
    multiIndexOrder (fun i => α (Fin.castAdd n i)) ≤ multiIndexOrder α := by
  rw [order_eq_sum, order_eq_sum, Fin.sum_univ_add]; omega

theorem order_natAdd_le {m n : Nat} (α : MultiIndex (m + n)) :
    multiIndexOrder (fun j => α (Fin.natAdd m j)) ≤ multiIndexOrder α := by
  rw [order_eq_sum, order_eq_sum, Fin.sum_univ_add]; omega

theorem tensor_congr {m n : Nat} {φ φ' : TestFunction m} {ψ ψ' : TestFunction n}
    {θ θ' : TestFunction (m + n)} (hφ : TestFunction.Equivalent φ φ')
    (hψ : TestFunction.Equivalent ψ ψ') (h : IsTensorTest φ ψ θ) (h' : IsTensorTest φ' ψ' θ') :
    TestFunction.Equivalent θ θ' := by
  intro α z
  refine RealCompute.equiv_trans (θ.derivative_valid α z)
    (RealCompute.mul_valid (φ.derivative_valid _ _) (ψ.derivative_valid _ _))
    (θ'.derivative_valid α z) (h α z) ?_
  refine RealCompute.equiv_trans
    (RealCompute.mul_valid (φ.derivative_valid _ _) (ψ.derivative_valid _ _))
    (RealCompute.mul_valid (φ'.derivative_valid _ _) (ψ'.derivative_valid _ _))
    (θ'.derivative_valid α z) ?_ (RealCompute.equiv_symm (h' α z))
  exact RealCompute.mul_equiv (φ.derivative_valid _ _) (φ'.derivative_valid _ _)
    (ψ.derivative_valid _ _) (ψ'.derivative_valid _ _) (hφ _ _) (hψ _ _)



open Classical in
noncomputable def val (x : RealCompute) : RealComputeQuotient.Value :=
  if h : x.Valid then RealComputeQuotient.ofRaw x h else 0

theorem val_of_valid {x : RealCompute} (hx : x.Valid) : val x = RealComputeQuotient.ofRaw x hx := by
  unfold val; rw [dif_pos hx]

theorem val_eq {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) (h : x.Equiv y) :
    val x = val y := by
  rw [val_of_valid hx, val_of_valid hy]; exact RealComputeQuotient.ofRaw_eq_ofRaw h

theorem equiv_of_val {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) (h : val x = val y) :
    x.Equiv y := by
  rw [val_of_valid hx, val_of_valid hy] at h; exact RealComputeQuotient.equiv_of_ofRaw_eq h

theorem val_mul {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    val (RealCompute.mul x y) = val x * val y := by
  rw [val_of_valid (x := RealCompute.mul x y) (RealCompute.mul_valid hx hy), val_of_valid hx, val_of_valid hy]; rfl

theorem val_add {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    val (RealCompute.add x y) = val x + val y := by
  rw [val_of_valid (x := RealCompute.add x y) (RealCompute.add_valid hx hy), val_of_valid hx, val_of_valid hy]; rfl

theorem val_add' {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    val (x + y) = val x + val y := val_add hx hy

theorem val_mul' {x y : RealCompute} (hx : x.Valid) (hy : y.Valid) :
    val (x * y) = val x * val y := val_mul hx hy

theorem ofRat_zero_valid : (RealCompute.ofRat 0).Valid := RealCompute.ofRat_valid 0

theorem val_zero : val (RealCompute.ofRat 0) = 0 := by
  rw [val_of_valid (x := RealCompute.ofRat 0) (RealCompute.ofRat_valid 0)]; rfl

theorem tdv {m n : Nat} {φ : TestFunction m} {ψ : TestFunction n} {θ : TestFunction (m + n)}
    (h : IsTensorTest φ ψ θ) (α : MultiIndex (m + n)) (z : QPoint (m + n)) :
    val (θ.derivative α z) =
      val (φ.derivative (fun i => α (Fin.castAdd n i)) (fun i => z (Fin.castAdd n i))) *
      val (ψ.derivative (fun j => α (Fin.natAdd m j)) (fun j => z (Fin.natAdd m j))) := by
  rw [← val_mul (φ.derivative_valid _ _) (ψ.derivative_valid _ _)]
  exact val_eq (θ.derivative_valid _ _)
    (RealCompute.mul_valid (φ.derivative_valid _ _) (ψ.derivative_valid _ _)) (h α z)

theorem left_zero {m n : Nat} {X : TestFunctionSpace m} {Z : TestFunctionSpace (m + n)}
    {ψ : TestFunction n} {θ : TestFunction (m + n)} (h : IsTensorTest X.zero ψ θ) :
    TestFunction.Equivalent θ Z.zero := by
  intro α z
  apply equiv_of_val (θ.derivative_valid _ _) (Z.zero.derivative_valid _ _)
  rw [tdv h, val_eq (Z.zero.derivative_valid _ _) ofRat_zero_valid
    (Z.zero_derivative α z), val_eq (X.zero.derivative_valid _ _) ofRat_zero_valid
    (X.zero_derivative _ _), val_zero]
  exact RealComputeQuotient.zero_mul _

theorem right_zero {m n : Nat} {Y : TestFunctionSpace n} {Z : TestFunctionSpace (m + n)}
    {φ : TestFunction m} {θ : TestFunction (m + n)} (h : IsTensorTest φ Y.zero θ) :
    TestFunction.Equivalent θ Z.zero := by
  intro α z
  apply equiv_of_val (θ.derivative_valid _ _) (Z.zero.derivative_valid _ _)
  rw [tdv h, val_eq (Z.zero.derivative_valid _ _) ofRat_zero_valid
    (Z.zero_derivative α z), val_eq (Y.zero.derivative_valid _ _) ofRat_zero_valid
    (Y.zero_derivative _ _), val_zero]
  exact RealComputeQuotient.mul_zero _

theorem left_add {m n : Nat} {X : TestFunctionSpace m} {Z : TestFunctionSpace (m + n)}
    {φ φ' : TestFunction m} {ψ : TestFunction n} {θ1 θ2 θ3 : TestFunction (m + n)}
    (h1 : IsTensorTest φ ψ θ1) (h2 : IsTensorTest φ' ψ θ2)
    (h3 : IsTensorTest (X.add φ φ') ψ θ3) :
    TestFunction.Equivalent θ3 (Z.add θ1 θ2) := by
  intro α z
  apply equiv_of_val (θ3.derivative_valid _ _) ((Z.add θ1 θ2).derivative_valid _ _)
  rw [tdv h3, val_eq ((Z.add θ1 θ2).derivative_valid _ _)
    (RealCompute.add_valid (θ1.derivative_valid _ _) (θ2.derivative_valid _ _))
    (Z.add_derivative θ1 θ2 α z), val_add' (θ1.derivative_valid _ _) (θ2.derivative_valid _ _),
    tdv h1, tdv h2,
    val_eq ((X.add φ φ').derivative_valid _ _)
      (RealCompute.add_valid (φ.derivative_valid _ _) (φ'.derivative_valid _ _))
      (X.add_derivative φ φ' _ _),
    val_add' (φ.derivative_valid _ _) (φ'.derivative_valid _ _)]
  exact RealComputeQuotient.add_mul _ _ _

theorem right_add {m n : Nat} {Y : TestFunctionSpace n} {Z : TestFunctionSpace (m + n)}
    {φ : TestFunction m} {ψ ψ' : TestFunction n} {θ1 θ2 θ3 : TestFunction (m + n)}
    (h1 : IsTensorTest φ ψ θ1) (h2 : IsTensorTest φ ψ' θ2)
    (h3 : IsTensorTest φ (Y.add ψ ψ') θ3) :
    TestFunction.Equivalent θ3 (Z.add θ1 θ2) := by
  intro α z
  apply equiv_of_val (θ3.derivative_valid _ _) ((Z.add θ1 θ2).derivative_valid _ _)
  rw [tdv h3, val_eq ((Z.add θ1 θ2).derivative_valid _ _)
    (RealCompute.add_valid (θ1.derivative_valid _ _) (θ2.derivative_valid _ _))
    (Z.add_derivative θ1 θ2 α z), val_add' (θ1.derivative_valid _ _) (θ2.derivative_valid _ _),
    tdv h1, tdv h2,
    val_eq ((Y.add ψ ψ').derivative_valid _ _)
      (RealCompute.add_valid (ψ.derivative_valid _ _) (ψ'.derivative_valid _ _))
      (Y.add_derivative ψ ψ' _ _),
    val_add' (ψ.derivative_valid _ _) (ψ'.derivative_valid _ _)]
  exact RealComputeQuotient.mul_add _ _ _

theorem left_scale {m n : Nat} {X : TestFunctionSpace m} {Z : TestFunctionSpace (m + n)}
    (r : RealCompute) (hr : r.Valid)
    {φ : TestFunction m} {ψ : TestFunction n} {θ1 θ3 : TestFunction (m + n)}
    (h1 : IsTensorTest φ ψ θ1) (h3 : IsTensorTest (X.scale r hr φ) ψ θ3) :
    TestFunction.Equivalent θ3 (Z.scale r hr θ1) := by
  intro α z
  apply equiv_of_val (θ3.derivative_valid _ _) ((Z.scale r hr θ1).derivative_valid _ _)
  rw [tdv h3, val_eq ((Z.scale r hr θ1).derivative_valid _ _)
    (RealCompute.mul_valid hr (θ1.derivative_valid _ _))
    (Z.scale_derivative r hr θ1 α z), val_mul hr (θ1.derivative_valid _ _),
    tdv h1,
    val_eq ((X.scale r hr φ).derivative_valid _ _)
      (RealCompute.mul_valid hr (φ.derivative_valid _ _))
      (X.scale_derivative r hr φ _ _),
    val_mul hr (φ.derivative_valid _ _)]
  exact RealComputeQuotient.mul_assoc _ _ _

theorem right_scale {m n : Nat} {Y : TestFunctionSpace n} {Z : TestFunctionSpace (m + n)}
    (r : RealCompute) (hr : r.Valid)
    {φ : TestFunction m} {ψ : TestFunction n} {θ1 θ3 : TestFunction (m + n)}
    (h1 : IsTensorTest φ ψ θ1) (h3 : IsTensorTest φ (Y.scale r hr ψ) θ3) :
    TestFunction.Equivalent θ3 (Z.scale r hr θ1) := by
  intro α z
  apply equiv_of_val (θ3.derivative_valid _ _) ((Z.scale r hr θ1).derivative_valid _ _)
  rw [tdv h3, val_eq ((Z.scale r hr θ1).derivative_valid _ _)
    (RealCompute.mul_valid hr (θ1.derivative_valid _ _))
    (Z.scale_derivative r hr θ1 α z), val_mul hr (θ1.derivative_valid _ _),
    tdv h1,
    val_eq ((Y.scale r hr ψ).derivative_valid _ _)
      (RealCompute.mul_valid hr (ψ.derivative_valid _ _))
      (Y.scale_derivative r hr ψ _ _),
    val_mul hr (ψ.derivative_valid _ _)]
  rw [← RealComputeQuotient.mul_assoc, ← RealComputeQuotient.mul_assoc,
    RealComputeQuotient.mul_comm (val _) (val r)]


theorem left_lin {m n : Nat} (X : TestFunctionSpace m) (Z : TestFunctionSpace (m + n))
    (K : Distribution Z) (T : TestFunction m → TestFunction n → TestFunction (m + n))
    (hT : ∀ φ ψ, IsTensorTest φ ψ (T φ ψ)) (ψ : TestFunction n) :
    IsLinearAction X (fun φ => K.action (T φ ψ)) where
  value_valid φ := K.action_valid _
  respects_test_equiv φ φ' h :=
    K.action_linear.respects_test_equiv _ _
      (tensor_congr h (TestFunction.equivalent_refl ψ) (hT φ ψ) (hT φ' ψ))
  map_zero :=
    RealCompute.equiv_trans (K.action_valid _) (K.action_valid _) (RealCompute.ofRat_valid 0)
      (K.action_linear.respects_test_equiv _ _ (left_zero (hT X.zero ψ)))
      K.action_linear.map_zero
  map_add φ φ' :=
    RealCompute.equiv_trans (K.action_valid _) (K.action_valid _)
      (RealCompute.add_valid (K.action_valid _) (K.action_valid _))
      (K.action_linear.respects_test_equiv _ _ (left_add (hT φ ψ) (hT φ' ψ) (hT _ ψ)))
      (K.action_linear.map_add _ _)
  map_scale r hr φ :=
    RealCompute.equiv_trans (K.action_valid _) (K.action_valid _)
      (RealCompute.mul_valid hr (K.action_valid _))
      (K.action_linear.respects_test_equiv _ _ (left_scale r hr (hT φ ψ) (hT _ ψ)))
      (K.action_linear.map_scale r hr _)

theorem right_lin {m n : Nat} (Y : TestFunctionSpace n) (Z : TestFunctionSpace (m + n))
    (K : Distribution Z) (T : TestFunction m → TestFunction n → TestFunction (m + n))
    (hT : ∀ φ ψ, IsTensorTest φ ψ (T φ ψ)) (φ : TestFunction m) :
    IsLinearAction Y (fun ψ => K.action (T φ ψ)) where
  value_valid ψ := K.action_valid _
  respects_test_equiv ψ ψ' h :=
    K.action_linear.respects_test_equiv _ _
      (tensor_congr (TestFunction.equivalent_refl φ) h (hT φ ψ) (hT φ ψ'))
  map_zero :=
    RealCompute.equiv_trans (K.action_valid _) (K.action_valid _) (RealCompute.ofRat_valid 0)
      (K.action_linear.respects_test_equiv _ _ (right_zero (hT φ Y.zero)))
      K.action_linear.map_zero
  map_add ψ ψ' :=
    RealCompute.equiv_trans (K.action_valid _) (K.action_valid _)
      (RealCompute.add_valid (K.action_valid _) (K.action_valid _))
      (K.action_linear.respects_test_equiv _ _ (right_add (hT φ ψ) (hT φ ψ') (hT φ _)))
      (K.action_linear.map_add _ _)
  map_scale r hr ψ :=
    RealCompute.equiv_trans (K.action_valid _) (K.action_valid _)
      (RealCompute.mul_valid hr (K.action_valid _))
      (K.action_linear.respects_test_equiv _ _ (right_scale r hr (hT φ ψ) (hT φ _)))
      (K.action_linear.map_scale r hr _)

def prodBox {m n : Nat} (B : RationalBox m) (C : RationalBox n) : RationalBox (m + n) where
  lower := Fin.append B.lower C.lower
  upper := Fin.append B.upper C.upper
  ordered := by
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [B.ordered j]
    · simp [C.ordered j]

theorem prodBox_contains {m n : Nat} (B : RationalBox m) (C : RationalBox n)
    (z : QPoint (m + n)) :
    (prodBox B C).Contains z ↔
      B.Contains (fun i => z (Fin.castAdd n i)) ∧ C.Contains (fun j => z (Fin.natAdd m j)) := by
  constructor
  · intro h
    exact ⟨fun i => by simpa [prodBox] using h (Fin.castAdd n i),
      fun j => by simpa [prodBox] using h (Fin.natAdd m j)⟩
  · rintro ⟨h1, h2⟩ i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa [prodBox] using h1 j
    · simpa [prodBox] using h2 j

theorem tensor_supported {m n : Nat} {B : RationalBox m} {C : RationalBox n}
    {φ : TestFunction m} {ψ : TestFunction n} {θ : TestFunction (m + n)}
    (h : IsTensorTest φ ψ θ) (hφ : φ.SupportedInBox B) (hψ : ψ.SupportedInBox C) :
    θ.SupportedInBox (prodBox B C) := by
  intro z hz
  have hz' := (prodBox_contains B C z).not.1 hz
  apply equiv_of_val (θ.value_valid z) ofRat_zero_valid
  unfold TestFunction.value
  rw [tdv h, val_zero]
  change val (φ.derivative (zeroIndex m) (fun i => z (Fin.castAdd n i))) *
    val (ψ.derivative (zeroIndex n) (fun j => z (Fin.natAdd m j))) = 0
  by_cases h1 : B.Contains (fun i => z (Fin.castAdd n i))
  · have h2 : ¬ C.Contains (fun j => z (Fin.natAdd m j)) := fun h2 => hz' ⟨h1, h2⟩
    have := val_eq (ψ.value_valid _) ofRat_zero_valid (hψ _ h2)
    unfold TestFunction.value at this
    exact (by rw [this, val_zero]; exact RealComputeQuotient.mul_zero _)
  · have := val_eq (φ.value_valid _) ofRat_zero_valid (hφ _ h1)
    unfold TestFunction.value at this
    exact (by rw [this, val_zero]; exact RealComputeQuotient.zero_mul _)

theorem tensor_bounded {m n : Nat} {φ : TestFunction m} {ψ : TestFunction n}
    {θ : TestFunction (m + n)} (h : IsTensorTest φ ψ θ) {N : Nat} {a b : Rat}
    (hφ : φ.DerivativesBoundedBy N a) (hψ : ψ.DerivativesBoundedBy N b) :
    θ.DerivativesBoundedBy N (a * b) := by
  intro α hα z
  have h1 := hφ _ (le_trans (order_castAdd_le α) hα) (fun i => z (Fin.castAdd n i))
  have h2 := hψ _ (le_trans (order_natAdd_le α) hα) (fun j => z (Fin.natAdd m j))
  exact small_congr _ _ (small_mul (φ.derivative_valid _ _) (ψ.derivative_valid _ _) h1 h2)
    (RealCompute.equiv_symm (h α z))
    |> fun x => by simpa using x

end KC

open KC in
theorem solution : ComputableDistributions.SchwartzKernelConverseTarget := by
  classical
  intro m n X Y Z K
  let T : TestFunction m → TestFunction n → TestFunction (m + n) :=
    fun φ ψ => Classical.choose (DistributionTheoryMission.tensor_tests m n φ ψ)
  have hT : ∀ φ ψ, IsTensorTest φ ψ (T φ ψ) :=
    fun φ ψ => Classical.choose_spec (DistributionTheoryMission.tensor_tests m n φ ψ)
  refine ⟨{ action := fun φ ψ => K.action (T φ ψ)
            linear_left := left_lin X Z K T hT
            linear_right := right_lin Y Z K T hT
            joint_bound := ?_ }, ?_⟩
  · intro B C
    obtain ⟨N, Ck, hC, h⟩ := K.action_continuous (prodBox B C)
    refine ⟨N, N, Ck, hC, ?_⟩
    intro φ ψ hφ hψ a b ha hb hφb hψb
    have := h (T φ ψ) (tensor_supported (hT φ ψ) hφ hψ) (a * b) (Rat.mul_nonneg ha hb)
      (tensor_bounded (hT φ ψ) hφb hψb)
    rw [← Rat.mul_assoc] at this
    exact this
  · intro φ ψ θ hθ
    exact K.action_linear.respects_test_equiv _ _
      (tensor_congr (TestFunction.equivalent_refl φ) (TestFunction.equivalent_refl ψ) hθ (hT φ ψ))
