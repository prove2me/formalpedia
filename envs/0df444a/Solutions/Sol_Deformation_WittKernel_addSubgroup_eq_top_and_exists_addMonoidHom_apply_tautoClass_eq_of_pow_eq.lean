-- Prove2me | solution 1 for Deformation.WittKernel.addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/138fc1ea-c268-5f88-b650-3c4ef5de02af

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_Dieudonne_WittGroupHopf
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import Definitions.Def_Dieudonne_WittKernelHopf
import Theorems.Thm_Deformation_convPow_eq_zero_and_isLocalRing_cartierDual_of_adjoin_coeff_wittHom_eq_top
import Theorems.Thm_MvPolynomial_finite_and_finrank_quotient_span_aeval_X_eq_pow_of_monic
import Theorems.Thm_MvPolynomial_finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow
import Theorems.Thm_Deformation_DieudonneModule_finrank_adjoin_coeff_le_natCard
import Theorems.Thm_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_WittKernel_addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false
set_option linter.unusedSectionVars false

universe v w

noncomputable section

open Function MvPolynomial

namespace WittKernelDieudonne

section Action

variable {T : Type*} [AddCommGroup T] (F V : AddMonoid.End T)

theorem comm_gens (hFV : F * V = V * F) :
    ∀ x ∈ ({F, V} : Set (AddMonoid.End T)), ∀ y ∈ ({F, V} : Set (AddMonoid.End T)), x * y = y * x := by
  intro x hx y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl <;> first | rfl | exact hFV | exact hFV.symm

open scoped IsMulCommutative in

def act (hFV : F * V = V * F) : MvPolynomial Bool ℤ →+* AddMonoid.End T :=
  haveI := Algebra.isMulCommutative_adjoin ℤ (comm_gens F V hFV)
  ((Algebra.adjoin ℤ ({F, V} : Set (AddMonoid.End T))).val.toRingHom).comp
    (MvPolynomial.aeval (R := ℤ) fun s : Bool =>
      (⟨if s then F else V, Algebra.subset_adjoin (by cases s <;> simp)⟩ :
        Algebra.adjoin ℤ ({F, V} : Set (AddMonoid.End T)))).toRingHom

@[scoped simp] theorem act_X (hFV : F * V = V * F) (s : Bool) :
    act F V hFV (MvPolynomial.X s) = if s then F else V := by
  simp [act]

theorem act_X_true (hFV : F * V = V * F) : act F V hFV (MvPolynomial.X true) = F := by
  rw [act_X]; rfl

theorem act_X_false (hFV : F * V = V * F) : act F V hFV (MvPolynomial.X false) = V := by
  rw [act_X]; rfl

@[scoped simp] theorem act_C_apply (hFV : F * V = V * F) (c : ℤ) (t : T) :
    act F V hFV (MvPolynomial.C c) t = c • t := by
  simp [act]

theorem act_mul_apply (hFV : F * V = V * F) (P Q : MvPolynomial Bool ℤ) (t : T) :
    act F V hFV (P * Q) t = act F V hFV P (act F V hFV Q t) := by
  rw [map_mul]; rfl

theorem act_mem (hFV : F * V = V * F) (N : AddSubgroup T) (hF : ∀ t ∈ N, F t ∈ N)
    (hV : ∀ t ∈ N, V t ∈ N) (P : MvPolynomial Bool ℤ) {t : T} (ht : t ∈ N) : act F V hFV P t ∈ N := by
  induction P using MvPolynomial.induction_on generalizing t with
  | C c => rw [act_C_apply]; exact N.zsmul_mem ht c
  | add P Q hP hQ => rw [map_add]; exact N.add_mem (hP ht) (hQ ht)
  | mul_X P s hP =>
    rw [act_mul_apply, act_X]
    cases s with
    | true => exact hP (hF t ht)
    | false => exact hP (hV t ht)

theorem act_apply_eq_zero_of_mem_span (hFV : F * V = V * F) (S : Set (MvPolynomial Bool ℤ)) (t : T)
    (hS : ∀ g ∈ S, act F V hFV g t = 0) {r : MvPolynomial Bool ℤ} (hr : r ∈ Ideal.span S) :
    act F V hFV r t = 0 := by
  induction hr using Submodule.span_induction with
  | mem g hg => exact hS g hg
  | zero => rw [map_zero]; rfl
  | add x y _ _ hx hy =>
    rw [map_add]
    change act F V hFV x t + act F V hFV y t = 0
    rw [hx, hy, add_zero]
  | smul s x _ hx => rw [smul_eq_mul, act_mul_apply, hx, map_zero]

theorem act_X_true_pow_apply (hFV : F * V = V * F) (m : ℕ) (t : T) :
    act F V hFV (MvPolynomial.X true ^ m) t = F^[m] t := by
  rw [map_pow, act_X_true, AddMonoid.End.coe_pow]

theorem act_X_false_pow_apply (hFV : F * V = V * F) (m : ℕ) (t : T) :
    act F V hFV (MvPolynomial.X false ^ m) t = V^[m] t := by
  rw [map_pow, act_X_false, AddMonoid.End.coe_pow]

variable {J : Type v} [Fintype J]

def combo (hFV : F * V = V * F) (t : J → T) : (J → MvPolynomial Bool ℤ) →+ T where
  toFun c := ∑ j, act F V hFV (c j) (t j)
  map_zero' := Finset.sum_eq_zero fun j _ => by rw [Pi.zero_apply, map_zero]; rfl
  map_add' c c' := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Pi.add_apply, map_add]; rfl

theorem combo_apply (hFV : F * V = V * F) (t : J → T) (c : J → MvPolynomial Bool ℤ) :
    combo F V hFV t c = ∑ j, act F V hFV (c j) (t j) := rfl

theorem combo_single [DecidableEq J] (hFV : F * V = V * F) (t : J → T) (j : J) :
    combo F V hFV t (Pi.single j 1) = t j := by
  rw [combo_apply, Finset.sum_eq_single j]
  · rw [Pi.single_eq_same, map_one]; rfl
  · intro j' _ hj'
    rw [Pi.single_eq_of_ne hj', map_zero]; rfl
  · intro h; exact absurd (Finset.mem_univ j) h

theorem combo_smul (hFV : F * V = V * F) (t : J → T) (r : MvPolynomial Bool ℤ)
    (c : J → MvPolynomial Bool ℤ) : combo F V hFV t (r • c) = act F V hFV r (combo F V hFV t c) := by
  rw [combo_apply, combo_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, act_mul_apply]

theorem F_combo (hFV : F * V = V * F) (t : J → T) (c : J → MvPolynomial Bool ℤ) :
    F (combo F V hFV t c) = combo F V hFV t ((MvPolynomial.X true : MvPolynomial Bool ℤ) • c) := by
  rw [combo_smul, act_X_true]

theorem V_combo (hFV : F * V = V * F) (t : J → T) (c : J → MvPolynomial Bool ℤ) :
    V (combo F V hFV t c) = combo F V hFV t ((MvPolynomial.X false : MvPolynomial Bool ℤ) • c) := by
  rw [combo_smul, act_X_false]

end Action

variable (p : ℕ) [hp : Fact p.Prime] (n a b : ℕ)

def Irel : Ideal (MvPolynomial Bool ℤ) :=
  Ideal.span ({MvPolynomial.X true * MvPolynomial.X false - MvPolynomial.C (p : ℤ),
    MvPolynomial.X false ^ n, MvPolynomial.X true ^ b - MvPolynomial.X true ^ a} : Set (MvPolynomial Bool ℤ))

variable {p n a b}

theorem act_apply_eq_zero_of_mem_Irel {T : Type*} [AddCommGroup T] (F V : AddMonoid.End T)
    (hFV : F * V = V * F) (t : T) (h1 : F (V t) = (p : ℤ) • t) (h2 : V^[n] t = 0)
    (h3 : F^[b] t = F^[a] t) {r : MvPolynomial Bool ℤ} (hr : r ∈ Irel p n a b) : act F V hFV r t = 0 := by
  refine act_apply_eq_zero_of_mem_span F V hFV _ t ?_ hr
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl | rfl
  · rw [map_sub]
    change act F V hFV (MvPolynomial.X true * MvPolynomial.X false) t - act F V hFV (MvPolynomial.C (p : ℤ)) t = 0
    rw [act_mul_apply, act_X_true, act_X_false, act_C_apply, h1, sub_self]
  · rw [act_X_false_pow_apply]; exact h2
  · rw [map_sub]
    change act F V hFV (MvPolynomial.X true ^ b) t - act F V hFV (MvPolynomial.X true ^ a) t = 0
    rw [act_X_true_pow_apply, act_X_true_pow_apply]
    exact sub_eq_zero.2 h3

variable (p n a b) (J : Type v) [Fintype J]

abbrev A : Type v := Deformation.WittKernel.Coord (ZMod p) p n a b J

abbrev M : Type v := Deformation.DieudonneModule (ZMod p) p (A p n a b J)

abbrev FM : AddMonoid.End (M p n a b J) := Deformation.DieudonneModule.frobenius (ZMod p) p (A p n a b J)

abbrev VM : AddMonoid.End (M p n a b J) := Deformation.DieudonneModule.verschiebung (ZMod p) p (A p n a b J)

abbrev τ (j : J) : M p n a b J := Deformation.WittKernel.tautoClass (ZMod p) p n a b J j

theorem FM_VM_comm : FM p n a b J * VM p n a b J = VM p n a b J * FM p n a b J := by
  refine AddMonoidHom.ext fun z => ?_
  change Deformation.DieudonneModule.frobenius (ZMod p) p _ (Deformation.DieudonneModule.verschiebung (ZMod p) p _ z) =
    Deformation.DieudonneModule.verschiebung (ZMod p) p _ (Deformation.DieudonneModule.frobenius (ZMod p) p _ z)
  rw [Deformation.DieudonneModule.frobenius_verschiebung, Deformation.DieudonneModule.verschiebung_frobenius]

def σ : (J → MvPolynomial Bool ℤ) →+ M p n a b J :=
  combo (FM p n a b J) (VM p n a b J) (FM_VM_comm p n a b J) (τ p n a b J)

def N : AddSubgroup (M p n a b J) := (σ p n a b J).range

variable {p n a b J}

theorem τ_mem_N (j : J) : τ p n a b J j ∈ N p n a b J := by
  classical
  exact ⟨Pi.single j 1, combo_single _ _ _ _ j⟩

theorem F_mem_N {z : M p n a b J} (hz : z ∈ N p n a b J) : FM p n a b J z ∈ N p n a b J := by
  obtain ⟨c, rfl⟩ := hz
  exact ⟨(MvPolynomial.X true : MvPolynomial Bool ℤ) • c, (F_combo _ _ _ _ c).symm⟩

theorem V_mem_N {z : M p n a b J} (hz : z ∈ N p n a b J) : VM p n a b J z ∈ N p n a b J := by
  obtain ⟨c, rfl⟩ := hz
  exact ⟨(MvPolynomial.X false : MvPolynomial Bool ℤ) • c, (V_combo _ _ _ _ c).symm⟩

theorem N_le (N' : AddSubgroup (M p n a b J)) (hF : ∀ z ∈ N', FM p n a b J z ∈ N') (hV : ∀ z ∈ N', VM p n a b J z ∈ N')
    (hτ : ∀ j, τ p n a b J j ∈ N') : N p n a b J ≤ N' := by
  rintro _ ⟨c, rfl⟩
  change ∑ j, act (FM p n a b J) (VM p n a b J) (FM_VM_comm p n a b J) (c j) (τ p n a b J j) ∈ N'
  exact N'.sum_mem fun j _ => act_mem _ _ _ N' hF hV (c j) (hτ j)

theorem act_τ_eq_zero {r : MvPolynomial Bool ℤ} (hr : r ∈ Irel p n a b) (j : J) :
    act (FM p n a b J) (VM p n a b J) (FM_VM_comm p n a b J) r (τ p n a b J j) = 0 := by
  refine act_apply_eq_zero_of_mem_Irel _ _ _ _ ?_ ?_ ?_ hr
  · exact Deformation.DieudonneModule.frobenius_verschiebung _
  · exact Deformation.WittKernel.verschiebung_iterate_tautoClass j
  · exact Deformation.WittKernel.frobenius_iterate_tautoClass j

theorem σ_eq_zero_of_forall_mem {c : J → MvPolynomial Bool ℤ} (hc : ∀ j, c j ∈ Irel p n a b) :
    σ p n a b J c = 0 := by
  change ∑ j, act (FM p n a b J) (VM p n a b J) (FM_VM_comm p n a b J) (c j) (τ p n a b J j) = 0
  exact Finset.sum_eq_zero fun j _ => act_τ_eq_zero (hc j) j

section Generation

variable (p n a b J)
variable [Fact (a < b)]

theorem isLocalRing_A : IsLocalRing (CartierDual (ZMod p) (A p n a b J)) :=
  (Deformation.convPow_eq_zero_and_isLocalRing_cartierDual_of_adjoin_coeff_wittHom_eq_top (ZMod p) p n
    (A p n a b J) Deformation.WittKernel.adjoin_coeff_wittHom_eq_top).2

theorem card_M_eq_finrank : Finite (M p n a b J) ∧ Nat.card (M p n a b J) = Module.finrank (ZMod p) (A p n a b J) := by
  obtain ⟨L, hfr, hcard⟩ :=
    Deformation.DieudonneModule.exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
      (ZMod p) p (A p n a b J) (isLocalRing_A p n a b J)
  rw [Nat.card_zmod] at hcard
  refine ⟨Nat.finite_of_card_ne_zero ?_, by rw [hcard, hfr]⟩
  rw [hcard]
  exact pow_ne_zero _ hp.out.ne_zero

scoped instance finite_M : Finite (M p n a b J) := (card_M_eq_finrank p n a b J).1

theorem finrank_le_card_N : Module.finrank (ZMod p) (A p n a b J) ≤ Nat.card (N p n a b J) := by
  have h := (Deformation.DieudonneModule.finrank_adjoin_coeff_le_natCard (ZMod p) p (A p n a b J)
    (N p n a b J) (fun z hz => F_mem_N hz) (fun z hz => V_mem_N hz)).2
  have htop : Algebra.adjoin (ZMod p) {c : A p n a b J | ∃ (m : ℕ) (x : Deformation.wittHom (ZMod p) p m (A p n a b J))
      (i : Fin m), Deformation.DieudonneModule.of (ZMod p) p (A p n a b J) m x ∈ N p n a b J ∧
        (x : TruncatedWittVector p m (A p n a b J)).coeff i = c} = ⊤ := by
    refine top_le_iff.1 (le_trans (le_of_eq Deformation.WittKernel.adjoin_coeff_tauto_eq_top.symm)
      (Algebra.adjoin_mono ?_))
    rintro _ ⟨j, i, rfl⟩
    exact ⟨n, Deformation.WittKernel.tauto (ZMod p) p n a b J j, i, τ_mem_N j, rfl⟩
  rw [htop] at h
  rwa [← (Subalgebra.topEquiv (R := ZMod p) (A := A p n a b J)).toLinearEquiv.finrank_eq]

theorem N_eq_top : N p n a b J = ⊤ := by
  refine AddSubgroup.eq_top_of_card_eq _ (le_antisymm ?_ ?_)
  · exact Nat.card_le_card_of_injective _ Subtype.val_injective
  · rw [(card_M_eq_finrank p n a b J).2]
    exact finrank_le_card_N p n a b J

theorem σ_surjective : Function.Surjective (σ p n a b J) := by
  intro z
  have hz : z ∈ N p n a b J := by rw [N_eq_top]; trivial
  exact hz

theorem finrank_A : Module.finrank (ZMod p) (A p n a b J) = (p ^ b) ^ (Nat.card J * n) := by
  have hab : a < b := Fact.out
  have hlt : p ^ a < p ^ b := Nat.pow_lt_pow_right hp.out.one_lt hab
  set f : Polynomial (ZMod p) := Polynomial.X ^ p ^ b - Polynomial.X ^ p ^ a with hf
  have hmonic : f.Monic :=
    Polynomial.monic_X_pow_sub (lt_of_le_of_lt (Polynomial.degree_X_pow_le _) (by exact_mod_cast hlt))
  have hdeg : f.natDegree = p ^ b := by
    rw [hf, Polynomial.natDegree_sub_eq_left_of_natDegree_lt, Polynomial.natDegree_X_pow]
    rwa [Polynomial.natDegree_X_pow, Polynomial.natDegree_X_pow]
  have hT := (MvPolynomial.finite_and_finrank_quotient_span_aeval_X_eq_pow_of_monic (ZMod p) (J × Fin n) f hmonic).2
  rw [hdeg, Nat.card_prod, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin] at hT
  have hI : Deformation.WittKernel.ideal (ZMod p) p n a b J =
      Ideal.span (Set.range fun ji : J × Fin n =>
        Polynomial.aeval (Deformation.WittGroup.X ji.1 ji.2 : Deformation.WittGroup.Coord (ZMod p) p n J) f) := by
    unfold Deformation.WittKernel.ideal
    congr 1
    congr 1
    funext ji
    rw [hf, map_sub, map_pow, map_pow, Polynomial.aeval_X]
    rfl
  rw [← hT]
  exact (Ideal.quotientEquivAlgOfEq (ZMod p) hI).toLinearEquiv.finrank_eq

def πE : (J → MvPolynomial Bool ℤ) →+ (J → MvPolynomial Bool ℤ ⧸ Irel p n a b) :=
  AddMonoidHom.pi fun j => (Ideal.Quotient.mk (Irel p n a b)).toAddMonoidHom.comp (Pi.evalAddMonoidHom _ j)

theorem πE_apply (c : J → MvPolynomial Bool ℤ) (j : J) : πE p n a b J c j = Ideal.Quotient.mk (Irel p n a b) (c j) := rfl

theorem mem_ker_πE {c : J → MvPolynomial Bool ℤ} : c ∈ (πE p n a b J).ker ↔ ∀ j, c j ∈ Irel p n a b := by
  rw [AddMonoidHom.mem_ker, funext_iff]
  refine forall_congr' fun j => ?_
  rw [πE_apply, Pi.zero_apply, Ideal.Quotient.eq_zero_iff_mem]

theorem πE_surjective : Function.Surjective (πE p n a b J) := fun c =>
  ⟨fun j => (Ideal.Quotient.mk_surjective (c j)).choose,
    funext fun j => (Ideal.Quotient.mk_surjective (c j)).choose_spec⟩

theorem ker_πE_le_ker_σ : (πE p n a b J).ker ≤ (σ p n a b J).ker := fun _ hc =>
  (AddMonoidHom.mem_ker).2 (σ_eq_zero_of_forall_mem ((mem_ker_πE p n a b J).1 hc))

def quotKerEquiv : (J → MvPolynomial Bool ℤ) ⧸ (σ p n a b J).ker ≃+ M p n a b J :=
  AddEquiv.ofBijective (QuotientAddGroup.kerLift (σ p n a b J))
    ⟨QuotientAddGroup.kerLift_injective _, fun z => by
      obtain ⟨c, rfl⟩ := σ_surjective p n a b J z
      exact ⟨QuotientAddGroup.mk c, QuotientAddGroup.kerLift_mk _ c⟩⟩

theorem quotKerEquiv_mk (c : J → MvPolynomial Bool ℤ) :
    quotKerEquiv p n a b J (QuotientAddGroup.mk c) = σ p n a b J c := by
  change QuotientAddGroup.kerLift (σ p n a b J) (QuotientAddGroup.mk c) = _
  exact QuotientAddGroup.kerLift_mk _ c

theorem finite_and_card_quot_ker_πE :
    Finite ((J → MvPolynomial Bool ℤ) ⧸ (πE p n a b J).ker) ∧
      Nat.card ((J → MvPolynomial Bool ℤ) ⧸ (πE p n a b J).ker) ≤ (p ^ (n * b)) ^ Nat.card J := by
  have hab : a < b := Fact.out
  obtain ⟨hfinE, hcardE⟩ :=
    MvPolynomial.finite_and_natCard_quotient_truncatedDieudonneRelations_le_pow p hp.out.pos n a b hab
  haveI : Finite (MvPolynomial Bool ℤ ⧸ Irel p n a b) := hfinE
  let e := QuotientAddGroup.quotientKerEquivOfSurjective (πE p n a b J) (πE_surjective p n a b J)
  refine ⟨Finite.of_equiv _ e.toEquiv.symm, ?_⟩
  rw [Nat.card_congr e.toEquiv, Nat.card_fun]
  exact Nat.pow_le_pow_left hcardE _

theorem ker_σ_eq : (σ p n a b J).ker = (πE p n a b J).ker := by
  refine le_antisymm ?_ (ker_πE_le_ker_σ p n a b J)

  obtain ⟨hfin, hcard⟩ := finite_and_card_quot_ker_πE p n a b J
  haveI := hfin
  let ω : (J → MvPolynomial Bool ℤ) ⧸ (πE p n a b J).ker →+ (J → MvPolynomial Bool ℤ) ⧸ (σ p n a b J).ker :=
    QuotientAddGroup.lift _ (QuotientAddGroup.mk' _)
      (by rw [QuotientAddGroup.ker_mk']; exact ker_πE_le_ker_σ p n a b J)
  have hω : Function.Surjective ω := by
    intro x
    obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ x
    exact ⟨QuotientAddGroup.mk c, QuotientAddGroup.lift_mk _ _ c⟩
  have hcard2 : Nat.card ((J → MvPolynomial Bool ℤ) ⧸ (σ p n a b J).ker) = (p ^ b) ^ (Nat.card J * n) := by
    rw [Nat.card_congr (quotKerEquiv p n a b J).toEquiv, (card_M_eq_finrank p n a b J).2, finrank_A]
  haveI : Finite ((J → MvPolynomial Bool ℤ) ⧸ (σ p n a b J).ker) := Finite.of_surjective ω hω
  have hle : Nat.card ((J → MvPolynomial Bool ℤ) ⧸ (πE p n a b J).ker) ≤
      Nat.card ((J → MvPolynomial Bool ℤ) ⧸ (σ p n a b J).ker) := by
    rw [hcard2]
    refine le_trans hcard (le_of_eq ?_)
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring
  have heq : Nat.card ((J → MvPolynomial Bool ℤ) ⧸ (πE p n a b J).ker) =
      Nat.card ((J → MvPolynomial Bool ℤ) ⧸ (σ p n a b J).ker) :=
    le_antisymm hle (Nat.card_le_card_of_surjective ω hω)
  obtain ⟨e⟩ := Finite.card_eq.1 heq
  have hinj : Function.Injective ω := hω.injective_of_finite e
  intro c hc
  have h1 : ω (QuotientAddGroup.mk c) = 0 := by
    change QuotientAddGroup.mk' _ c = 0
    exact (QuotientAddGroup.eq_zero_iff c).2 hc
  have h2 : (QuotientAddGroup.mk c : (J → MvPolynomial Bool ℤ) ⧸ (πE p n a b J).ker) = 0 :=
    hinj (by rw [h1, map_zero])
  exact (QuotientAddGroup.eq_zero_iff c).1 h2

theorem forall_mem_Irel_of_σ_eq_zero {c : J → MvPolynomial Bool ℤ} (hc : σ p n a b J c = 0) :
    ∀ j, c j ∈ Irel p n a b := by
  have h : c ∈ (σ p n a b J).ker := hc
  rw [ker_σ_eq] at h
  exact (mem_ker_πE p n a b J).1 h

end Generation

section Universal

variable (p n a b J)
variable [Fact (a < b)]
variable {D : Type w} [AddCommGroup D] (MD : Deformation.DieudonneDatum (p : ℤ) D)
  (hV : MD.V ^ n = 0) (hF : MD.F ^ b = MD.F ^ a) (d : J → D)

abbrev FD : AddMonoid.End D := MD.F.toAddMonoidHom
abbrev VD : AddMonoid.End D := MD.V.toAddMonoidHom

theorem FD_VD_comm : FD p MD * VD p MD = VD p MD * FD p MD := by
  refine AddMonoidHom.ext fun x => ?_
  change MD.F (MD.V x) = MD.V (MD.F x)
  rw [MD.F_V_apply, MD.V_F_apply]

def ρtilde : (J → MvPolynomial Bool ℤ) →+ D := combo (FD p MD) (VD p MD) (FD_VD_comm p MD) d

theorem linearMap_pow_apply (f : D →ₗ[ℤ] D) (m : ℕ) (x : D) : (f ^ m) x = (f.toAddMonoidHom : D → D)^[m] x := by
  rw [Module.End.pow_apply]; rfl

include hV hF in

theorem act_D_eq_zero {r : MvPolynomial Bool ℤ} (hr : r ∈ Irel p n a b) (x : D) :
    act (FD p MD) (VD p MD) (FD_VD_comm p MD) r x = 0 := by
  refine act_apply_eq_zero_of_mem_Irel _ _ _ x ?_ ?_ ?_ hr
  · exact MD.F_V_apply x
  · have := LinearMap.congr_fun hV x
    rwa [linearMap_pow_apply, LinearMap.zero_apply] at this
  · have := LinearMap.congr_fun hF x
    rwa [linearMap_pow_apply, linearMap_pow_apply] at this

include hV hF in
theorem ker_σ_le_ker_ρtilde : (σ p n a b J).ker ≤ (ρtilde p J MD d).ker := by
  intro c hc
  have hcI := forall_mem_Irel_of_σ_eq_zero p n a b J hc
  rw [AddMonoidHom.mem_ker]
  change ∑ j, act (FD p MD) (VD p MD) (FD_VD_comm p MD) (c j) (d j) = 0
  exact Finset.sum_eq_zero fun j _ => act_D_eq_zero p n a b MD hV hF (hcI j) (d j)

def ρ : M p n a b J →+ D :=
  (QuotientAddGroup.lift (σ p n a b J).ker (ρtilde p J MD d) (ker_σ_le_ker_ρtilde p n a b J MD hV hF d)).comp
    (quotKerEquiv p n a b J).symm.toAddMonoidHom

theorem ρ_σ (c : J → MvPolynomial Bool ℤ) : ρ p n a b J MD hV hF d (σ p n a b J c) = ρtilde p J MD d c := by
  unfold ρ
  rw [AddMonoidHom.comp_apply]
  have h : (quotKerEquiv p n a b J).symm (σ p n a b J c) = QuotientAddGroup.mk c := by
    rw [AddEquiv.symm_apply_eq, quotKerEquiv_mk]
  change QuotientAddGroup.lift _ _ _ ((quotKerEquiv p n a b J).symm (σ p n a b J c)) = _
  rw [h, QuotientAddGroup.lift_mk]

theorem ρ_frobenius (z : M p n a b J) :
    ρ p n a b J MD hV hF d (Deformation.DieudonneModule.frobenius (ZMod p) p _ z) = MD.F (ρ p n a b J MD hV hF d z) := by
  obtain ⟨c, rfl⟩ := σ_surjective p n a b J z
  have h1 : Deformation.DieudonneModule.frobenius (ZMod p) p _ (σ p n a b J c) =
      σ p n a b J ((MvPolynomial.X true : MvPolynomial Bool ℤ) • c) :=
    F_combo _ _ _ _ c
  rw [h1, ρ_σ, ρ_σ]
  exact (F_combo (FD p MD) (VD p MD) (FD_VD_comm p MD) d c).symm

theorem ρ_verschiebung (z : M p n a b J) :
    ρ p n a b J MD hV hF d (Deformation.DieudonneModule.verschiebung (ZMod p) p _ z) = MD.V (ρ p n a b J MD hV hF d z) := by
  obtain ⟨c, rfl⟩ := σ_surjective p n a b J z
  have h1 : Deformation.DieudonneModule.verschiebung (ZMod p) p _ (σ p n a b J c) =
      σ p n a b J ((MvPolynomial.X false : MvPolynomial Bool ℤ) • c) :=
    V_combo _ _ _ _ c
  rw [h1, ρ_σ, ρ_σ]
  exact (V_combo (FD p MD) (VD p MD) (FD_VD_comm p MD) d c).symm

theorem ρ_τ (j : J) : ρ p n a b J MD hV hF d (τ p n a b J j) = d j := by
  classical
  have h1 : τ p n a b J j = σ p n a b J (Pi.single j 1) := (combo_single _ _ _ _ j).symm
  rw [h1, ρ_σ]
  exact combo_single _ _ _ _ j

end Universal

end WittKernelDieudonne
p2m_reactivate "P2MW.S_Deformation_WittKernel_addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq.WittKernelDieudonne"

end
p2m_reactivate "P2MW.S_Deformation_WittKernel_addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq.WittKernelDieudonne"

theorem solution
    (p : ℕ) [Fact p.Prime] (n a b : ℕ) (hab : a < b) (J : Type v) [Finite J]
    {D : Type w} [AddCommGroup D] (MD : Deformation.DieudonneDatum (p : ℤ) D)
    (hV : MD.V ^ n = 0) (hF : MD.F ^ b = MD.F ^ a) (d : J → D) :
    (∀ N : AddSubgroup (Deformation.DieudonneModule (ZMod p) p
        (Deformation.WittKernel.Coord (ZMod p) p n a b J)),
      (∀ z ∈ N, Deformation.DieudonneModule.frobenius (ZMod p) p _ z ∈ N) →
      (∀ z ∈ N, Deformation.DieudonneModule.verschiebung (ZMod p) p _ z ∈ N) →
      (∀ j, Deformation.WittKernel.tautoClass (ZMod p) p n a b J j ∈ N) → N = ⊤) ∧
    ∃ ρ : Deformation.DieudonneModule (ZMod p) p (Deformation.WittKernel.Coord (ZMod p) p n a b J) →+ D,
      (∀ z, ρ (Deformation.DieudonneModule.frobenius (ZMod p) p _ z) = MD.F (ρ z)) ∧
      (∀ z, ρ (Deformation.DieudonneModule.verschiebung (ZMod p) p _ z) = MD.V (ρ z)) ∧
      ∀ j, ρ (Deformation.WittKernel.tautoClass (ZMod p) p n a b J j) = d j := by
  haveI : Fintype J := Fintype.ofFinite J
  haveI : Fact (a < b) := ⟨hab⟩
  refine ⟨fun N hFN hVN hτN => ?_, ⟨WittKernelDieudonne.ρ p n a b J MD hV hF d,
    WittKernelDieudonne.ρ_frobenius p n a b J MD hV hF d,
    WittKernelDieudonne.ρ_verschiebung p n a b J MD hV hF d,
    WittKernelDieudonne.ρ_τ p n a b J MD hV hF d⟩⟩
  refine top_le_iff.1 ?_
  rw [← WittKernelDieudonne.N_eq_top p n a b J]
  exact WittKernelDieudonne.N_le N hFN hVN hτN

end S_Deformation_WittKernel_addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq
end P2MW
export P2MW.S_Deformation_WittKernel_addSubgroup_eq_top_and_exists_addMonoidHom_apply_tautoClass_eq_of_pow_eq (solution)
