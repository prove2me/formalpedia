-- Prove2me | solution 1 for CohCarrier.diamondRaw_comm
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/c11f53bc-7e35-5afb-a363-f37d66f317d0

import Definitions.Def_CohCarrier_Lower
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Group
import Mathlib.Data.Nat.Prime.Int
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_diamondRaw_comm

set_option autoImplicit false
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace IharaSolRQ

open CohCarrier

variable {Γ : Type} [Group Γ] (S : Subgroup Γ)

theorem coe_slip (q : Quotient (QuotientGroup.rightRel S)) (γ : Γ) :
    (slip S q γ : Γ) = rep S q * γ * (rep S (cls S (rep S q * γ)))⁻¹ := rfl

theorem cls_rep_mul (x δ : Γ) : cls S (rep S (cls S x) * δ) = cls S (x * δ) := by
  apply Quotient.sound'
  have h : QuotientGroup.rightRel S (rep S (cls S x)) x := Quotient.exact' (by simp [rep, cls])
  rw [QuotientGroup.rightRel_apply] at h ⊢
  simpa [mul_assoc] using h

noncomputable def mulRight (γ : Γ) :
    Quotient (QuotientGroup.rightRel S) ≃ Quotient (QuotientGroup.rightRel S) where
  toFun := Quotient.map' (· * γ) fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢; simpa [mul_assoc] using h
  invFun := Quotient.map' (· * γ⁻¹) fun x y h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢; simpa [mul_assoc] using h
  left_inv q := Quotient.inductionOn' q fun x => by simp [Quotient.map'_mk'', mul_assoc]
  right_inv q := Quotient.inductionOn' q fun x => by simp [Quotient.map'_mk'', mul_assoc]

theorem mulRight_eq_cls_rep_mul (γ : Γ) (x : Quotient (QuotientGroup.rightRel S)) :
    mulRight S γ x = cls S (rep S x * γ) := by
  induction x using Quotient.inductionOn' with
  | h y =>
    show cls S (y * γ) = cls S (rep S (cls S y) * γ)
    exact (cls_rep_mul S y γ).symm

def toRight : Γ ⧸ S ≃ Quotient (QuotientGroup.rightRel S) :=
  (QuotientGroup.quotientRightRelEquivQuotientLeftRel S).symm

noncomputable def secL (p : Γ ⧸ S) : Γ := (rep S (toRight S p))⁻¹

theorem secL_spec (p : Γ ⧸ S) : (QuotientGroup.mk (secL S p) : Γ ⧸ S) = p := by
  induction p using QuotientGroup.induction_on with
  | H g =>
    show (QuotientGroup.mk ((rep S (cls S g⁻¹))⁻¹) : Γ ⧸ S) = QuotientGroup.mk g
    have h : QuotientGroup.rightRel S (rep S (cls S g⁻¹)) g⁻¹ := Quotient.exact' (by simp [rep, cls])
    rw [QuotientGroup.rightRel_apply] at h
    rw [QuotientGroup.eq, inv_inv]
    simpa [mul_assoc] using S.inv_mem h

theorem toRight_inv_smul (γ : Γ) (p : Γ ⧸ S) :
    toRight S (γ⁻¹ • p) = cls S (rep S (toRight S p) * γ) := by
  induction p using QuotientGroup.induction_on with
  | H g =>
    show cls S (γ⁻¹ * g)⁻¹ = cls S (rep S (cls S g⁻¹) * γ)
    rw [cls_rep_mul, mul_inv_rev, inv_inv]

noncomputable def transL : S.LeftTransversal :=
  ⟨Set.range (secL S), Subgroup.isComplement_range_left (secL_spec S)⟩

theorem transL_apply (p : Γ ⧸ S) : ((transL S).2.leftQuotientEquiv p : Γ) = secL S p :=
  Subgroup.IsComplement.leftQuotientEquiv_apply (secL_spec S) p

theorem toAdditiveLeft_transfer_apply [S.FiniteIndex] {V : Type} [AddCommGroup V]
    (ψ : ↥S →* Multiplicative V) (g : Γ) :
    MonoidHom.toAdditiveLeft (MonoidHom.transfer ψ) (Additive.ofMul g) =
      ∑ q : Quotient (QuotientGroup.rightRel S), (ψ (slip S q g)).toAdd := by
  have hdiff : Subgroup.leftTransversals.diff ψ (transL S) (g • transL S) =
      ∏ p : Γ ⧸ S, ψ (slip S (toRight S p) g) := by
    unfold Subgroup.leftTransversals.diff
    refine Fintype.prod_congr _ _ fun p => congrArg ψ (Subtype.ext ?_)
    show ((transL S).2.leftQuotientEquiv p : Γ)⁻¹ * ((g • transL S).2.leftQuotientEquiv p : Γ) = _
    rw [Subgroup.smul_apply_eq_smul_apply_inv_smul, transL_apply, transL_apply, smul_eq_mul,
      coe_slip]
    simp only [secL, inv_inv]
    rw [toRight_inv_smul, mul_assoc]
  show ((MonoidHom.transfer ψ) g).toAdd = _
  rw [MonoidHom.transfer_def ψ (transL S) g, hdiff, toAdd_prod]
  exact Fintype.sum_equiv (toRight S) _ _ fun p => rfl

open scoped MatrixGroups

theorem heckeT_apply_eq_sum_rq (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]
    {V : Type} [AddCommGroup V] (F : Additive ↥(GammaH M H) →+ V) (γ : ↥(GammaH M H)) :
    heckeT M H ℓ V F (Additive.ofMul γ) =
      ∑ q : Quotient (QuotientGroup.rightRel (GammaHUpper M H ℓ)),
        F (Additive.ofMul (conjL M H ℓ (slip (GammaHUpper M H ℓ) q γ))) :=
  toAdditiveLeft_transfer_apply (GammaHUpper M H ℓ)
    ((AddMonoidHom.toMultiplicativeRight F).comp (conjL M H ℓ)) γ

end IharaSolRQ

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

namespace IharaSolComm

variable {G : Type*} [Group G] {Γ : Type*} [Group Γ] (ι : Γ →* G)

structure HeckeFamily where

  K : Type
  [instFintype : Fintype K]

  δ : K → G

  act : K → Γ → K

  η : K → Γ → Γ
  transport : ∀ (k : K) (γ : Γ), δ k * ι γ = ι (η k γ) * δ (act k γ)
  act_one : ∀ k : K, act k 1 = k
  act_mul : ∀ (k : K) (γ γ' : Γ), act k (γ * γ') = act (act k γ) γ'
  η_mul : ∀ (k : K) (γ γ' : Γ), η k (γ * γ') = η k γ * η (act k γ) γ'

attribute [scoped instance] HeckeFamily.instFintype

namespace HeckeFamily

variable {ι}
variable (D : HeckeFamily ι)

theorem η_one (k : D.K) : D.η k 1 = 1 := by
  have h := D.η_mul k 1 1
  rw [mul_one, D.act_one] at h
  exact left_eq_mul.mp h

def actEquiv (γ : Γ) : D.K ≃ D.K where
  toFun k := D.act k γ
  invFun k := D.act k γ⁻¹
  left_inv k := by show D.act (D.act k γ) γ⁻¹ = k; rw [← D.act_mul, mul_inv_cancel, D.act_one]
  right_inv k := by show D.act (D.act k γ⁻¹) γ = k; rw [← D.act_mul, inv_mul_cancel, D.act_one]

@[scoped simp] theorem actEquiv_apply (γ : Γ) (k : D.K) : D.actEquiv γ k = D.act k γ := rfl

section Operator

variable (A : Type*) [AddCommGroup A]

noncomputable def T (F : Additive Γ →+ A) : Additive Γ →+ A where
  toFun g := ∑ k : D.K, F (Additive.ofMul (D.η k g.toMul))
  map_zero' := by simp [η_one]
  map_add' g g' := by
    have hmul : (g + g').toMul = g.toMul * g'.toMul := rfl
    simp only [hmul, D.η_mul, ofMul_mul, map_add, Finset.sum_add_distrib]
    congr 1
    exact Fintype.sum_equiv (D.actEquiv (g.toMul)) _ _ fun k => rfl

theorem T_apply (F : Additive Γ →+ A) (g : Additive Γ) :
    D.T A F g = ∑ k : D.K, F (Additive.ofMul (D.η k g.toMul)) := rfl

theorem T_add (F F' : Additive Γ →+ A) : D.T A (F + F') = D.T A F + D.T A F' :=
  AddMonoidHom.ext fun g => by
    simp only [T_apply, AddMonoidHom.add_apply, Finset.sum_add_distrib]

theorem T_zero : D.T A 0 = 0 :=
  AddMonoidHom.ext fun g => by
    simp only [T_apply, AddMonoidHom.zero_apply, Finset.sum_const_zero]

end Operator

def Distinct : Prop := ∀ k k' : D.K, D.δ k * (D.δ k')⁻¹ ∈ ι.range → k = k'

variable {D} in

theorem Distinct.eq_of_mul_eq (hD : D.Distinct) {a b : D.K} {γ₁ γ₂ : G} (h₁ : γ₁ ∈ ι.range) (h₂ : γ₂ ∈ ι.range)
    (h : γ₁ * D.δ a = γ₂ * D.δ b) : a = b := by
  apply hD
  have hδ : D.δ a = γ₁⁻¹ * (γ₂ * D.δ b) := eq_inv_mul_of_mul_eq h
  have : D.δ a * (D.δ b)⁻¹ = γ₁⁻¹ * γ₂ := by
    rw [hδ, mul_assoc, mul_assoc, mul_inv_cancel, mul_one]
  rw [this]
  exact ι.range.mul_mem (ι.range.inv_mem h₁) h₂

def ofDistinct (hι : Function.Injective ι) (K : Type) [Fintype K] (δ : K → G) (act : K → Γ → K) (η : K → Γ → Γ)
    (transport : ∀ (k : K) (γ : Γ), δ k * ι γ = ι (η k γ) * δ (act k γ))
    (distinct : ∀ k k' : K, δ k * (δ k')⁻¹ ∈ ι.range → k = k') : HeckeFamily ι where
  K := K
  δ := δ
  act := act
  η := η
  transport := transport
  act_one k := by
    apply distinct
    have h := transport k 1
    rw [map_one, mul_one] at h
    rw [h, _root_.mul_inv_rev, mul_inv_cancel_left]
    exact ι.range.inv_mem ⟨η k 1, rfl⟩
  act_mul k γ γ' := by

    have h1 : δ k * ι (γ * γ') = ι (η k (γ * γ')) * δ (act k (γ * γ')) := transport k (γ * γ')
    have h2 : δ k * ι (γ * γ') = ι (η k γ * η (act k γ) γ') * δ (act (act k γ) γ') := by
      rw [map_mul, ← mul_assoc, transport k γ, mul_assoc, transport (act k γ) γ', ← mul_assoc, ← map_mul]
    apply distinct
    have h3 : δ (act k (γ * γ')) = (ι (η k (γ * γ')))⁻¹ * (ι (η k γ * η (act k γ) γ') *
        δ (act (act k γ) γ')) := by rw [← h2, h1, inv_mul_cancel_left]
    rw [h3, ← mul_assoc, mul_inv_cancel_right]
    exact ι.range.mul_mem (ι.range.inv_mem ⟨_, rfl⟩) ⟨_, rfl⟩
  η_mul k γ γ' := by
    have h1 : δ k * ι (γ * γ') = ι (η k (γ * γ')) * δ (act k (γ * γ')) := transport k (γ * γ')
    have h2 : δ k * ι (γ * γ') = ι (η k γ * η (act k γ) γ') * δ (act (act k γ) γ') := by
      rw [map_mul, ← mul_assoc, transport k γ, mul_assoc, transport (act k γ) γ', ← mul_assoc, ← map_mul]

    have hidx : act k (γ * γ') = act (act k γ) γ' := by
      apply distinct
      have h3 : δ (act k (γ * γ')) = (ι (η k (γ * γ')))⁻¹ * (ι (η k γ * η (act k γ) γ') *
          δ (act (act k γ) γ')) := by rw [← h2, h1, inv_mul_cancel_left]
      rw [h3, ← mul_assoc, mul_inv_cancel_right]
      exact ι.range.mul_mem (ι.range.inv_mem ⟨_, rfl⟩) ⟨_, rfl⟩
    rw [hidx] at h1
    exact hι (mul_right_cancel (h1.symm.trans h2))

def comp (D D' : HeckeFamily ι) : HeckeFamily ι where
  K := D.K × D'.K
  δ p := D'.δ p.2 * D.δ p.1
  act p γ := (D.act p.1 γ, D'.act p.2 (D.η p.1 γ))
  η p γ := D'.η p.2 (D.η p.1 γ)
  transport p γ := by
    show D'.δ p.2 * D.δ p.1 * ι γ = ι (D'.η p.2 (D.η p.1 γ)) * (D'.δ (D'.act p.2 (D.η p.1 γ)) * D.δ (D.act p.1 γ))
    rw [mul_assoc, D.transport, ← mul_assoc, D'.transport, mul_assoc]
  act_one p := by
    show (D.act p.1 1, D'.act p.2 (D.η p.1 1)) = p
    rw [D.η_one, D.act_one, D'.act_one]
  act_mul p γ γ' := by
    show (D.act p.1 (γ * γ'), D'.act p.2 (D.η p.1 (γ * γ'))) =
      (D.act (D.act p.1 γ) γ', D'.act (D'.act p.2 (D.η p.1 γ)) (D.η (D.act p.1 γ) γ'))
    rw [D.act_mul, D.η_mul, D'.act_mul]
  η_mul p γ γ' := by
    show D'.η p.2 (D.η p.1 (γ * γ')) =
      D'.η p.2 (D.η p.1 γ) * D'.η (D'.act p.2 (D.η p.1 γ)) (D.η (D.act p.1 γ) γ')
    rw [D.η_mul, D'.η_mul]

theorem T_comp (D D' : HeckeFamily ι) (A : Type*) [AddCommGroup A] (F : Additive Γ →+ A) :
    D.T A (D'.T A F) = (D.comp D').T A F := by
  refine AddMonoidHom.ext fun g => ?_

  show ∑ k : D.K, (D'.T A F) (Additive.ofMul (D.η k g.toMul)) =
    ∑ p : D.K × D'.K, F (Additive.ofMul (D'.η p.2 (D.η p.1 g.toMul)))
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [T_apply]
  rfl

section RepIndep

variable {D}
variable (hι : Function.Injective ι) {D₂ : HeckeFamily ι} (hD₂ : D₂.Distinct) (π : D.K ≃ D₂.K) (ε : D.K → Γ)
  (hε : ∀ k : D.K, D₂.δ (π k) = ι (ε k) * D.δ k)

include hι hD₂ hε in

theorem act_eq_of_sameCosets (k : D.K) (γ : Γ) :
    D₂.act (π k) γ = π (D.act k γ) ∧ D₂.η (π k) γ = ε k * D.η k γ * (ε (D.act k γ))⁻¹ := by

  have h1 : D₂.δ (π k) * ι γ = ι (D₂.η (π k) γ) * D₂.δ (D₂.act (π k) γ) := D₂.transport (π k) γ
  have h2 : D₂.δ (π k) * ι γ = ι (ε k * D.η k γ * (ε (D.act k γ))⁻¹) * D₂.δ (π (D.act k γ)) := by
    rw [hε k, mul_assoc, D.transport k γ, hε (D.act k γ)]
    simp only [map_mul, map_inv, mul_assoc, inv_mul_cancel_left]
  have hidx : D₂.act (π k) γ = π (D.act k γ) :=
    hD₂.eq_of_mul_eq ⟨_, rfl⟩ ⟨_, rfl⟩ (h1.symm.trans h2)
  refine ⟨hidx, ?_⟩
  rw [hidx] at h1
  exact hι (mul_right_cancel (h1.symm.trans h2))

include hι hD₂ hε in

theorem T_eq_of_sameCosets (A : Type*) [AddCommGroup A] (F : Additive Γ →+ A) : D.T A F = D₂.T A F := by
  refine AddMonoidHom.ext fun g => ?_
  rw [T_apply, T_apply]

  rw [← Fintype.sum_equiv π (fun k => F (Additive.ofMul (D₂.η (π k) g.toMul)))
    (fun k₂ => F (Additive.ofMul (D₂.η k₂ g.toMul))) (fun _ => rfl)]
  have hterm : ∀ k : D.K, F (Additive.ofMul (D₂.η (π k) g.toMul)) =
      F (Additive.ofMul (ε k)) + F (Additive.ofMul (D.η k g.toMul)) - F (Additive.ofMul (ε (D.act k g.toMul))) := by
    intro k
    rw [(act_eq_of_sameCosets hι hD₂ π ε hε k g.toMul).2, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg,
      sub_eq_add_neg]
  simp only [hterm, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [Fintype.sum_equiv (D.actEquiv g.toMul) (fun k => F (Additive.ofMul (ε (D.act k g.toMul))))
    (fun k => F (Additive.ofMul (ε k))) (fun _ => rfl)]
  abel

end RepIndep

theorem T_comm_of_sameCosets (hι : Function.Injective ι) (D D' : HeckeFamily ι) (hdist : (D'.comp D).Distinct)
    (π : (D.comp D').K ≃ (D'.comp D).K) (ε : (D.comp D').K → Γ)
    (hε : ∀ p, (D'.comp D).δ (π p) = ι (ε p) * (D.comp D').δ p)
    (A : Type*) [AddCommGroup A] (F : Additive Γ →+ A) :
    D.T A (D'.T A F) = D'.T A (D.T A F) := by
  rw [T_comp, T_comp]
  exact T_eq_of_sameCosets hι hdist π ε hε A F

end HeckeFamily
p2m_reactivate "P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm.HeckeFamily"

end IharaSolComm
p2m_reactivate "P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm.HeckeFamily P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm"

namespace IharaSolComm

open scoped MatrixGroups

section DockHeckeT

def ιQ : SL(2, ℤ) →* GL (Fin 2) ℚ :=
  Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map (Int.castRingHom ℚ))

@[scoped simp] theorem ιQ_coe_apply (g : SL(2, ℤ)) (i j : Fin 2) :
    ((ιQ g : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j = ((g i j : ℤ) : ℚ) := rfl

theorem ιQ_injective : Function.Injective ιQ := fun g g' h => by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hij := congrArg (fun u : GL (Fin 2) ℚ => (u : Matrix (Fin 2) (Fin 2) ℚ) i j) h
  simpa using hij

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ) [NeZero ℓ]

def ιΓ : ↥(CohCarrier.GammaH M H) →* GL (Fin 2) ℚ := ιQ.comp (CohCarrier.GammaH M H).subtype

omit [NeZero ℓ] in
theorem ιΓ_injective : Function.Injective (ιΓ M H) := ιQ_injective.comp Subtype.val_injective

omit [NeZero ℓ] in
@[scoped simp] theorem ιΓ_coe_apply (γ : ↥(CohCarrier.GammaH M H)) (i j : Fin 2) :
    ((ιΓ M H γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) i j = (((γ : SL(2, ℤ)) i j : ℤ) : ℚ) := rfl

def alpha : GL (Fin 2) ℚ where
  val := !![1, 0; 0, (ℓ : ℚ)]
  inv := !![1, 0; 0, (ℓ : ℚ)⁻¹]
  val_inv := by
    have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [hℓ]
  inv_val := by
    have hℓ : (ℓ : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne ℓ)
    rw [Matrix.mul_fin_two, Matrix.one_fin_two]
    simp [hℓ]

@[scoped simp] theorem alpha_coe : ((alpha ℓ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = !![1, 0; 0, (ℓ : ℚ)] := rfl

theorem alpha_mul_ιΓ (s : ↥(CohCarrier.GammaHUpper M H ℓ)) :
    alpha ℓ * ιΓ M H (s : ↥(CohCarrier.GammaH M H)) = ιΓ M H (CohCarrier.conjL M H ℓ s) * alpha ℓ := by
  have hdvd : (ℓ : ℤ) ∣ ((s : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) 0 1 :=
    CohCarrier.dvd_of_mem_GammaHUpper M H ℓ s
  have e01 : ((((s : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) 0 1 / (ℓ : ℤ) : ℤ) : ℚ) * (ℓ : ℚ) =
      ((((s : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) 0 1 : ℤ) : ℚ) := by
    rw [← Int.cast_natCast (R := ℚ) ℓ, ← Int.cast_mul, Int.ediv_mul_cancel hdvd]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, alpha_coe, ιΓ_coe_apply]
  fin_cases i <;> fin_cases j <;>
    simp [CohCarrier.conjL, CohCarrier.conjUpperMat, e01, mul_comm]

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

omit [NeZero ℓ] in

theorem eq_of_rep_mul_inv_mem (S : Subgroup ↥(CohCarrier.GammaH M H)) (q q' : Quotient (QuotientGroup.rightRel S))
    (h : CohCarrier.rep S q * (CohCarrier.rep S q')⁻¹ ∈ S) : q = q' := by
  have hrel : QuotientGroup.rightRel S (CohCarrier.rep S q') (CohCarrier.rep S q) := by
    rw [QuotientGroup.rightRel_apply]
    exact h
  have hq := Quotient.sound' hrel
  rw [show CohCarrier.rep S q' = q'.out from rfl, show CohCarrier.rep S q = q.out from rfl,
    Quotient.out_eq', Quotient.out_eq'] at hq
  exact hq.symm

theorem alpha_rep_distinct (q q' : Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ)))
    (hqq' : alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q) *
      (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q'))⁻¹ ∈ (ιΓ M H).range) : q = q' := by
  obtain ⟨γ₀, hγ₀⟩ := hqq'
  have hg : ιΓ M H γ₀ * alpha ℓ = alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q *
      (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q')⁻¹) := by
    rw [map_mul, map_inv, hγ₀, _root_.mul_inv_rev]
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  have h01 := congrArg (fun u : GL (Fin 2) ℚ => (u : Matrix (Fin 2) (Fin 2) ℚ) 0 1) hg
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, alpha_coe, ιΓ_coe_apply] at h01
  simp at h01
  have hz : ((γ₀ : SL(2, ℤ)) 0 1) * (ℓ : ℤ) =
      (((CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q * (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q')⁻¹ :
        ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) 0 1) := by
    exact_mod_cast h01
  have hdvd : (ℓ : ℤ) ∣ (((CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q *
      (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q')⁻¹ : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) 0 1) :=
    Dvd.intro_left _ hz
  refine eq_of_rep_mul_inv_mem M H _ q q' ?_
  rw [Subgroup.mem_subgroupOf, CohCarrier.mem_Gamma0Upper]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ).mpr hdvd

noncomputable def famT : HeckeFamily (ιΓ M H) :=
  HeckeFamily.ofDistinct (ιΓ_injective M H)
    (Quotient (QuotientGroup.rightRel (CohCarrier.GammaHUpper M H ℓ)))
    (fun q => alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q))
    (fun q (γ : ↥(CohCarrier.GammaH M H)) =>
      CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q * γ))
    (fun q (γ : ↥(CohCarrier.GammaH M H)) =>
      CohCarrier.conjL M H ℓ (CohCarrier.slip (CohCarrier.GammaHUpper M H ℓ) q γ))
    (by
      intro q γ
      have hs : ((CohCarrier.slip (CohCarrier.GammaHUpper M H ℓ) q γ : ↥(CohCarrier.GammaHUpper M H ℓ)) :
            ↥(CohCarrier.GammaH M H)) *
          CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ)
            (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q * γ)) = CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q * γ := by
        show CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q * γ *
            (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ)
              (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q * γ)))⁻¹ *
          CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ)
            (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q * γ)) = CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q * γ
        rw [inv_mul_cancel_right]
      have key : ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q) * ιΓ M H γ =
          ιΓ M H ((CohCarrier.slip (CohCarrier.GammaHUpper M H ℓ) q γ : ↥(CohCarrier.GammaHUpper M H ℓ)) :
            ↥(CohCarrier.GammaH M H)) *
            ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ)
              (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q * γ))) := by
        rw [← map_mul, ← map_mul, hs]
      show alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q) * ιΓ M H γ =
        ιΓ M H (CohCarrier.conjL M H ℓ (CohCarrier.slip (CohCarrier.GammaHUpper M H ℓ) q γ)) *
          (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ)
            (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q * γ))))
      rw [mul_assoc, key, ← mul_assoc, alpha_mul_ιΓ, mul_assoc])
    (alpha_rep_distinct M H ℓ)

theorem heckeT_eq_famT (V : Type) [AddCommGroup V] (F : Additive ↥(CohCarrier.GammaH M H) →+ V) :
    CohCarrier.heckeT M H ℓ V F = (famT M H ℓ).T V F := by
  refine AddMonoidHom.ext fun g => ?_
  rw [HeckeFamily.T_apply]
  exact IharaSolRQ.heckeT_apply_eq_sum_rq M H ℓ F g.toMul

end DockHeckeT
p2m_reactivate "P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm.HeckeFamily P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm"

section CC3

def αZ (n : ℕ) : Matrix (Fin 2) (Fin 2) ℤ := !![1, 0; 0, (n : ℤ)]

@[scoped simp] theorem αZ_00 (n : ℕ) : αZ n 0 0 = 1 := rfl
@[scoped simp] theorem αZ_01 (n : ℕ) : αZ n 0 1 = 0 := rfl
@[scoped simp] theorem αZ_10 (n : ℕ) : αZ n 1 0 = 0 := rfl
@[scoped simp] theorem αZ_11 (n : ℕ) : αZ n 1 1 = (n : ℤ) := rfl

theorem alpha_val (n : ℕ) [NeZero n] :
    ((alpha n : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) = (αZ n).map (Int.castRingHom ℚ) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [αZ]

theorem ιΓ_val (M : ℕ) (H : Subgroup (ZMod M)ˣ) (γ : ↥(CohCarrier.GammaH M H)) :
    ((ιΓ M H γ : GL (Fin 2) ℚ) : Matrix (Fin 2) (Fin 2) ℚ) =
      ((γ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ) := rfl

theorem comp_famT_distinct (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']
    (hcop : Nat.Coprime ℓ ℓ') : ((famT M H ℓ').comp (famT M H ℓ)).Distinct := by
  rintro ⟨k, j⟩ ⟨k₂, j₂⟩ ⟨γ₀, hγ₀⟩
  change ιΓ M H γ₀ = (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) j) *
      (alpha ℓ' * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k))) *
    (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) j₂) *
      (alpha ℓ' * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k₂)))⁻¹ at hγ₀
  generalize hA : CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) j = A at hγ₀
  generalize hB : CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) j₂ = B at hγ₀
  generalize hT₁ : CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k = T₁ at hγ₀
  generalize hT₂ : CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k₂ = T₂ at hγ₀

  have E : ιΓ M H γ₀ * (alpha ℓ * (ιΓ M H B * (alpha ℓ' * ιΓ M H T₂))) =
      alpha ℓ * (ιΓ M H A * (alpha ℓ' * ιΓ M H T₁)) := by
    have h := eq_mul_inv_iff_mul_eq.mp hγ₀
    simpa only [mul_assoc] using h
  have E'' : ιΓ M H γ₀ * (alpha ℓ * (ιΓ M H B * alpha ℓ')) =
      alpha ℓ * (ιΓ M H A * (alpha ℓ' * ιΓ M H (T₁ * T₂⁻¹))) := by
    refine mul_right_cancel (b := ιΓ M H T₂) ?_
    simpa only [map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one] using E
  generalize hG : T₁ * T₂⁻¹ = G at E''

  have EZ : ((γ₀ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (αZ ℓ * (((B : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * αZ ℓ')) =
      αZ ℓ * (((A : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ) * (αZ ℓ' * ((G : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ))) := by
    apply Matrix.map_injective (f := ⇑(Int.castRingHom ℚ)) Int.cast_injective
    simp only [Matrix.map_mul, ← ιΓ_val, ← alpha_val, ← Units.val_mul]
    exact congrArg Units.val E''
  have e01 := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℤ => N 0 1) EZ
  have e11 := congrArg (fun N : Matrix (Fin 2) (Fin 2) ℤ => N 1 1) EZ
  simp only [Matrix.mul_apply, Fin.sum_univ_two, αZ_00, αZ_01, αZ_10, αZ_11, mul_zero, one_mul, zero_mul,
    add_zero, zero_add] at e01 e11

  have hd0 : (ℓ' : ℤ) ∣ (A : SL(2, ℤ)) 0 0 * (G : SL(2, ℤ)) 0 1 :=
    ⟨(γ₀ : SL(2, ℤ)) 0 0 * (B : SL(2, ℤ)) 0 1 + (ℓ : ℤ) * (γ₀ : SL(2, ℤ)) 0 1 * (B : SL(2, ℤ)) 1 1 -
      (A : SL(2, ℤ)) 0 1 * (G : SL(2, ℤ)) 1 1, by linear_combination (-1 : ℤ) * e01⟩
  have hd1 : (ℓ' : ℤ) ∣ (ℓ : ℤ) * ((A : SL(2, ℤ)) 1 0 * (G : SL(2, ℤ)) 0 1) :=
    ⟨(γ₀ : SL(2, ℤ)) 1 0 * (B : SL(2, ℤ)) 0 1 + (ℓ : ℤ) * (γ₀ : SL(2, ℤ)) 1 1 * (B : SL(2, ℤ)) 1 1 -
      (ℓ : ℤ) * (A : SL(2, ℤ)) 1 1 * (G : SL(2, ℤ)) 1 1, by linear_combination (-1 : ℤ) * e11⟩
  have hcopZ : IsCoprime (ℓ' : ℤ) (ℓ : ℤ) := (Nat.isCoprime_iff_coprime.mpr hcop).symm
  have hd1' : (ℓ' : ℤ) ∣ (A : SL(2, ℤ)) 1 0 * (G : SL(2, ℤ)) 0 1 := hcopZ.dvd_of_dvd_mul_left hd1
  have hdet : (A : SL(2, ℤ)) 0 0 * (A : SL(2, ℤ)) 1 1 - (A : SL(2, ℤ)) 0 1 * (A : SL(2, ℤ)) 1 0 = 1 := by
    have h := (A : SL(2, ℤ)).det_coe
    rwa [Matrix.det_fin_two] at h
  have hG01 : (ℓ' : ℤ) ∣ (G : SL(2, ℤ)) 0 1 := by
    have hre : (G : SL(2, ℤ)) 0 1 = (A : SL(2, ℤ)) 1 1 * ((A : SL(2, ℤ)) 0 0 * (G : SL(2, ℤ)) 0 1) -
        (A : SL(2, ℤ)) 0 1 * ((A : SL(2, ℤ)) 1 0 * (G : SL(2, ℤ)) 0 1) := by
      linear_combination (-((G : SL(2, ℤ)) 0 1)) * hdet
    rw [hre]
    exact dvd_sub (dvd_mul_of_dvd_right hd0 _) (dvd_mul_of_dvd_right hd1' _)

  have hmem : T₁ * T₂⁻¹ ∈ CohCarrier.GammaHUpper M H ℓ' := by
    rw [Subgroup.mem_subgroupOf, CohCarrier.mem_Gamma0Upper, hG]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ ℓ').mpr hG01
  have hk : k = k₂ :=
    eq_of_rep_mul_inv_mem M H (CohCarrier.GammaHUpper M H ℓ') k k₂ (by rw [hT₁, hT₂]; exact hmem)
  subst hk
  have hT : T₂ = T₁ := hT₂.symm.trans hT₁
  subst hT

  subst hG
  have E3 : ιΓ M H γ₀ * (alpha ℓ * ιΓ M H B) = alpha ℓ * ιΓ M H A := by
    refine mul_right_cancel (b := alpha ℓ') ?_
    simpa only [mul_inv_cancel, map_one, mul_one, mul_assoc] using E''
  have hj : j = j₂ :=
    alpha_rep_distinct M H ℓ j j₂ ⟨γ₀, by rw [hA, hB, eq_mul_inv_iff_mul_eq]; exact E3⟩
  subst hj
  rfl

def SameCosetsComm (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ'] : Prop :=
  ((famT M H ℓ').comp (famT M H ℓ)).Distinct ∧
    ∃ (π : ((famT M H ℓ).comp (famT M H ℓ')).K ≃ ((famT M H ℓ').comp (famT M H ℓ)).K)
      (ε : ((famT M H ℓ).comp (famT M H ℓ')).K → ↥(CohCarrier.GammaH M H)),
      ∀ p, ((famT M H ℓ').comp (famT M H ℓ)).δ (π p) = ιΓ M H (ε p) * ((famT M H ℓ).comp (famT M H ℓ')).δ p

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

theorem heckeT_comm_of_sameCosetsComm (h : SameCosetsComm M H ℓ ℓ') (V : Type) [AddCommGroup V]
    (F : Additive ↥(CohCarrier.GammaH M H) →+ V) :
    CohCarrier.heckeT M H ℓ V (CohCarrier.heckeT M H ℓ' V F) =
      CohCarrier.heckeT M H ℓ' V (CohCarrier.heckeT M H ℓ V F) := by
  obtain ⟨hdist, π, ε, hε⟩ := h
  simp only [heckeT_eq_famT]
  exact HeckeFamily.T_comm_of_sameCosets (ιΓ_injective M H) (famT M H ℓ) (famT M H ℓ') hdist π ε hε V F

end CC3
p2m_reactivate "P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm.HeckeFamily P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm"

namespace HeckeFamily

theorem sameCosets_of_exhibit {Γ G : Type*} [Group Γ] [Group G] {ι : Γ →* G}
    (D₁ D₂ : HeckeFamily ι) (h₂ : D₂.Distinct) (hcard : Fintype.card D₂.K = Fintype.card D₁.K)
    (f : D₂.K → D₁.K) (ε : D₂.K → Γ) (hf : ∀ k, D₁.δ (f k) = ι (ε k) * D₂.δ k) :
    ∃ (π : D₂.K ≃ D₁.K) (ε' : D₂.K → Γ), ∀ k, D₁.δ (π k) = ι (ε' k) * D₂.δ k := by
  have hinj : Function.Injective f := by
    intro k k' hkk'
    apply h₂
    refine ⟨(ε k)⁻¹ * ε k', ?_⟩
    have e1 : D₂.δ k = (ι (ε k))⁻¹ * D₁.δ (f k) := by rw [hf k, inv_mul_cancel_left]
    have e2 : D₂.δ k' = (ι (ε k'))⁻¹ * D₁.δ (f k') := by rw [hf k', inv_mul_cancel_left]
    rw [e1, e2, hkk', _root_.mul_inv_rev, inv_inv, map_mul, map_inv, mul_assoc, mul_inv_cancel_left]
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩
  exact ⟨Equiv.ofBijective f hbij, ε, fun k => hf k⟩

end HeckeFamily
p2m_reactivate "P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm.HeckeFamily P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm"

section Diamond

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem ιQ_mul_ιΓ (σ : Gamma0 M) (γ : ↥(CohCarrier.GammaH M H)) :
    ιQ (σ : SL(2, ℤ)) * ιΓ M H γ = ιΓ M H (CohCarrier.conjHom M H σ γ) * ιQ (σ : SL(2, ℤ)) := by
  show ιQ (σ : SL(2, ℤ)) * ιQ (γ : SL(2, ℤ)) =
    ιQ ((σ : SL(2, ℤ)) * (γ : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹) * ιQ (σ : SL(2, ℤ))
  rw [map_mul, map_mul, map_inv, inv_mul_cancel_right]

def famD (σ : Gamma0 M) : HeckeFamily (ιΓ M H) where
  K := Unit
  δ _ := ιQ (σ : SL(2, ℤ))
  act _ _ := ()
  η _ γ := CohCarrier.conjHom M H σ γ
  transport _ γ := ιQ_mul_ιΓ M H σ γ
  act_one _ := rfl
  act_mul _ _ _ := rfl
  η_mul _ γ γ' := map_mul (CohCarrier.conjHom M H σ) γ γ'

theorem diamondRaw_eq_famD (σ : Gamma0 M) (V : Type) [AddCommGroup V] (F : Additive ↥(CohCarrier.GammaH M H) →+ V) :
    CohCarrier.diamondRaw M H V σ F = (famD M H σ).T V F := by
  refine AddMonoidHom.ext fun g => ?_
  show _ = ∑ _k : Unit, F (Additive.ofMul (CohCarrier.conjHom M H σ g.toMul))
  rw [Fintype.sum_unique]
  rfl

theorem diamondRaw_congr (σ σ' : Gamma0 M) (h : (σ' : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ ∈ CohCarrier.GammaH M H)
    (V : Type) [AddCommGroup V] (F : Additive ↥(CohCarrier.GammaH M H) →+ V) :
    CohCarrier.diamondRaw M H V σ' F = CohCarrier.diamondRaw M H V σ F := by
  refine AddMonoidHom.ext fun g => ?_
  have key : CohCarrier.conjHom M H σ' g.toMul =
      (⟨_, h⟩ : ↥(CohCarrier.GammaH M H)) * CohCarrier.conjHom M H σ g.toMul * (⟨_, h⟩ : ↥(CohCarrier.GammaH M H))⁻¹ := by
    apply Subtype.ext
    show (σ' : SL(2, ℤ)) * (g.toMul : SL(2, ℤ)) * (σ' : SL(2, ℤ))⁻¹ =
      (σ' : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ * ((σ : SL(2, ℤ)) * (g.toMul : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹) *
        ((σ' : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹)⁻¹
    group
  show F (Additive.ofMul (CohCarrier.conjHom M H σ' g.toMul)) = F (Additive.ofMul (CohCarrier.conjHom M H σ g.toMul))
  rw [key, ofMul_mul, ofMul_mul, ofMul_inv, map_add, map_add, map_neg]
  abel

variable (ℓ : ℕ) [NeZero ℓ]

omit [NeZero ℓ] in
theorem dvd_of_dvd_mulLevel (σ : Gamma0 M) (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0) :
    (ℓ : ℤ) ∣ (σ : SL(2, ℤ)) 1 0 :=
  dvd_trans (Int.natCast_dvd_natCast.mpr (dvd_mul_right ℓ M)) hσ

def sigmaLow (σ : Gamma0 M) (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0) : Gamma0 M :=
  ⟨CohCarrier.conjLowerMat ℓ (σ : SL(2, ℤ)) (dvd_of_dvd_mulLevel M ℓ σ hσ), by
    obtain ⟨t, ht⟩ := hσ
    have hq : (σ : SL(2, ℤ)) 1 0 / (ℓ : ℤ) = (M : ℤ) * t := by
      rw [ht, Nat.cast_mul, mul_assoc, Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr (NeZero.ne ℓ))]
    rw [Gamma0_mem]
    simp [CohCarrier.conjLowerMat, hq]⟩

@[scoped simp] theorem sigmaLow_coe (σ : Gamma0 M) (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0) :
    ((sigmaLow M ℓ σ hσ : Gamma0 M) : SL(2, ℤ)) = CohCarrier.conjLowerMat ℓ (σ : SL(2, ℤ)) (dvd_of_dvd_mulLevel M ℓ σ hσ) :=
  rfl

theorem gamma0Units_sigmaLow (σ : Gamma0 M) (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0) :
    CohCarrier.gamma0Units M (sigmaLow M ℓ σ hσ) = CohCarrier.gamma0Units M σ := by
  apply Units.ext
  simp [CohCarrier.gamma0Units, Gamma0Map, sigmaLow, CohCarrier.conjLowerMat]

theorem ιQ_mul_alpha (σ : Gamma0 M) (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0) :
    ιQ (σ : SL(2, ℤ)) * alpha ℓ = alpha ℓ * ιQ ((sigmaLow M ℓ σ hσ : Gamma0 M) : SL(2, ℤ)) := by
  have hdvd := dvd_of_dvd_mulLevel M ℓ σ hσ
  have e10 : (ℓ : ℚ) * ((((σ : SL(2, ℤ)) 1 0 / (ℓ : ℤ) : ℤ)) : ℚ) = (((σ : SL(2, ℤ)) 1 0 : ℤ) : ℚ) := by
    rw [← Int.cast_natCast (R := ℚ) ℓ, ← Int.cast_mul, Int.mul_ediv_cancel' hdvd]
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, alpha_coe, ιQ_coe_apply, sigmaLow_coe]
  fin_cases i <;> fin_cases j <;>
    simp [CohCarrier.conjLowerMat, e10, mul_comm]

noncomputable def sfac (S : Subgroup ↥(CohCarrier.GammaH M H)) (g : ↥(CohCarrier.GammaH M H)) : S :=
  ⟨g * (CohCarrier.rep S (CohCarrier.cls S g))⁻¹, by
    have h : QuotientGroup.rightRel S (CohCarrier.rep S (CohCarrier.cls S g)) g :=
      Quotient.exact' (by simp [CohCarrier.rep, CohCarrier.cls])
    rw [QuotientGroup.rightRel_apply] at h
    exact h⟩

theorem sfac_spec (S : Subgroup ↥(CohCarrier.GammaH M H)) (g : ↥(CohCarrier.GammaH M H)) :
    (sfac M H S g : ↥(CohCarrier.GammaH M H)) * CohCarrier.rep S (CohCarrier.cls S g) = g :=
  inv_mul_cancel_right _ _

def gDiaSL (σ : Gamma0 M) (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0) (t : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ) :=
  ((sigmaLow M ℓ σ hσ : Gamma0 M) : SL(2, ℤ)) * (t : SL(2, ℤ)) * ((σ : SL(2, ℤ)))⁻¹

theorem gDiaSL_mem_Gamma0 (σ : Gamma0 M) (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0) (t : ↥(CohCarrier.GammaH M H)) :
    gDiaSL M H ℓ σ hσ t ∈ Gamma0 M :=
  Subgroup.mul_mem _ (Subgroup.mul_mem _ (sigmaLow M ℓ σ hσ).2 (CohCarrier.GammaH_le_Gamma0 H t.2))
    (Subgroup.inv_mem _ σ.2)

theorem gDiaSL_mem (σ : Gamma0 M) (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0) (t : ↥(CohCarrier.GammaH M H)) :
    gDiaSL M H ℓ σ hσ t ∈ CohCarrier.GammaH M H := by
  obtain ⟨ht0, ht⟩ := CohCarrier.mem_GammaH_iff.mp t.2
  refine CohCarrier.mem_GammaH_iff.mpr ⟨gDiaSL_mem_Gamma0 M H ℓ σ hσ t, ?_⟩
  have e : (⟨gDiaSL M H ℓ σ hσ t, gDiaSL_mem_Gamma0 M H ℓ σ hσ t⟩ : Gamma0 M) =
      sigmaLow M ℓ σ hσ * ⟨(t : SL(2, ℤ)), ht0⟩ * σ⁻¹ :=
    Subtype.ext rfl
  rw [e, map_mul, map_mul, map_inv, gamma0Units_sigmaLow, mul_comm (CohCarrier.gamma0Units M σ) _, mul_inv_cancel_right]
  exact ht

def gDia (σ : Gamma0 M) (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0) (t : ↥(CohCarrier.GammaH M H)) :
    ↥(CohCarrier.GammaH M H) :=
  ⟨gDiaSL M H ℓ σ hσ t, gDiaSL_mem M H ℓ σ hσ t⟩

@[scoped simp] theorem gDia_coe (σ : Gamma0 M) (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0) (t : ↥(CohCarrier.GammaH M H)) :
    ((gDia M H ℓ σ hσ t : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) =
      ((sigmaLow M ℓ σ hσ : Gamma0 M) : SL(2, ℤ)) * (t : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹ :=
  rfl

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem heckeDiamond_impl (σ : Gamma0 M) (hσ : ((ℓ * M : ℕ) : ℤ) ∣ (σ : SL(2, ℤ)) 1 0)
    (V : Type) [AddCommGroup V] (F : Additive ↥(CohCarrier.GammaH M H) →+ V) :
    CohCarrier.heckeT M H ℓ V (CohCarrier.diamondRaw M H V σ F) =
      CohCarrier.diamondRaw M H V σ (CohCarrier.heckeT M H ℓ V F) := by
  rw [diamondRaw_eq_famD, diamondRaw_eq_famD]
  simp only [heckeT_eq_famT]

  have hdist : ((famD M H σ).comp (famT M H ℓ)).Distinct := by
    rintro ⟨u, q⟩ ⟨u', q'⟩ ⟨γ₀, hγ₀⟩
    change ιΓ M H γ₀ = alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q) * ιQ (σ : SL(2, ℤ)) *
      (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q') * ιQ (σ : SL(2, ℤ)))⁻¹ at hγ₀
    have hq : q = q' := alpha_rep_distinct M H ℓ q q' ⟨γ₀, by rw [hγ₀]; group⟩
    subst hq
    rfl
  have h₂ : ((famT M H ℓ).comp (famD M H σ)).Distinct := by
    rintro ⟨q, u⟩ ⟨q', u'⟩ ⟨γ₀, hγ₀⟩
    change ιΓ M H γ₀ = ιQ (σ : SL(2, ℤ)) * (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q)) *
      (ιQ (σ : SL(2, ℤ)) * (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q')))⁻¹ at hγ₀
    have key := ιQ_mul_ιΓ M H σ⁻¹ γ₀
    have hq : q = q' := alpha_rep_distinct M H ℓ q q' ⟨CohCarrier.conjHom M H σ⁻¹ γ₀, by
      have e : ιΓ M H (CohCarrier.conjHom M H σ⁻¹ γ₀) =
          ιQ ((σ⁻¹ : Gamma0 M) : SL(2, ℤ)) * ιΓ M H γ₀ * (ιQ ((σ⁻¹ : Gamma0 M) : SL(2, ℤ)))⁻¹ := by
        rw [key, mul_inv_cancel_right]
      rw [e, hγ₀, Subgroup.coe_inv, map_inv]
      group⟩
    subst hq
    rfl
  have hcard : Fintype.card ((famT M H ℓ).comp (famD M H σ)).K = Fintype.card ((famD M H σ).comp (famT M H ℓ)).K :=
    Fintype.card_congr (Equiv.prodComm _ _)

  obtain ⟨π, ε, hε⟩ := HeckeFamily.sameCosets_of_exhibit ((famD M H σ).comp (famT M H ℓ)) ((famT M H ℓ).comp (famD M H σ))
    h₂ hcard
    (fun p => ((), CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ)
      (gDia M H ℓ σ hσ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) p.1))))
    (fun p => ((CohCarrier.conjL M H ℓ (sfac M H (CohCarrier.GammaHUpper M H ℓ)
      (gDia M H ℓ σ hσ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) p.1))))⁻¹ : ↥(CohCarrier.GammaH M H)))
    (by
      rintro ⟨q, u⟩
      change alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ)
            (gDia M H ℓ σ hσ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q)))) * ιQ (σ : SL(2, ℤ)) =
        ιΓ M H ((CohCarrier.conjL M H ℓ (sfac M H (CohCarrier.GammaHUpper M H ℓ)
            (gDia M H ℓ σ hσ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q))))⁻¹ : ↥(CohCarrier.GammaH M H)) *
          (ιQ (σ : SL(2, ℤ)) * (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q)))
      generalize hg : gDia M H ℓ σ hσ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q) = g
      have hgσ : ιΓ M H g * ιQ (σ : SL(2, ℤ)) =
          ιQ ((sigmaLow M ℓ σ hσ : Gamma0 M) : SL(2, ℤ)) * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q) := by
        rw [← hg]
        show ιQ ((gDia M H ℓ σ hσ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q) : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ)) *
            ιQ (σ : SL(2, ℤ)) =
          ιQ ((sigmaLow M ℓ σ hσ : Gamma0 M) : SL(2, ℤ)) *
            ιQ ((CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q : ↥(CohCarrier.GammaH M H)) : SL(2, ℤ))
        rw [gDia_coe, map_mul, map_mul, map_inv, inv_mul_cancel_right]
      have hs := sfac_spec M H (CohCarrier.GammaHUpper M H ℓ) g
      generalize hsd : sfac M H (CohCarrier.GammaHUpper M H ℓ) g = s at hs ⊢
      have hιg : ιΓ M H g = ιΓ M H (s : ↥(CohCarrier.GammaH M H)) *
          ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ) g)) := by
        rw [← map_mul, hs]
      have chain : ιQ (σ : SL(2, ℤ)) * (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) q)) =
          ιΓ M H (CohCarrier.conjL M H ℓ s : ↥(CohCarrier.GammaH M H)) *
            (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ) g)) *
              ιQ (σ : SL(2, ℤ))) := by
        rw [← mul_assoc, ιQ_mul_alpha M ℓ σ hσ, mul_assoc, ← hgσ, hιg]
        simp only [← mul_assoc, alpha_mul_ιΓ]
      rw [chain, map_inv, inv_mul_cancel_left])
  exact HeckeFamily.T_comm_of_sameCosets (ιΓ_injective M H) (famT M H ℓ) (famD M H σ) hdist π ε hε V F

end Diamond
p2m_reactivate "P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm.HeckeFamily P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm"

section CC3b

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

def TwoSidedReduction : Prop :=
  ∀ g : ↥(CohCarrier.GammaH M H), ∃ γ₁ γ₂ γ₃ : ↥(CohCarrier.GammaH M H),
    alpha ℓ' * ιΓ M H g * alpha ℓ = ιΓ M H γ₁ * alpha ℓ * ιΓ M H γ₂ * alpha ℓ' * ιΓ M H γ₃

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

theorem sameCosetsComm_of_twoSided (hcop : Nat.Coprime ℓ ℓ') (hX : TwoSidedReduction M H ℓ ℓ') :
    SameCosetsComm M H ℓ ℓ' := by
  refine ⟨comp_famT_distinct M H ℓ ℓ' hcop, ?_⟩
  choose γ₁ γ₂ γ₃ hγ using hX
  have h₂ : ((famT M H ℓ).comp (famT M H ℓ')).Distinct := comp_famT_distinct M H ℓ' ℓ hcop.symm
  have hcard : Fintype.card ((famT M H ℓ).comp (famT M H ℓ')).K = Fintype.card ((famT M H ℓ').comp (famT M H ℓ)).K :=
    Fintype.card_congr (Equiv.prodComm _ _)
  obtain ⟨π, ε, hε⟩ := HeckeFamily.sameCosets_of_exhibit ((famT M H ℓ').comp (famT M H ℓ)) ((famT M H ℓ).comp (famT M H ℓ'))
    h₂ hcard
    (fun p => ((CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ') (γ₃ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') p.2) * (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) p.1))), (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ) (γ₂ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') p.2) * (CohCarrier.conjL M H ℓ' (sfac M H (CohCarrier.GammaHUpper M H ℓ') (γ₃ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') p.2) * (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) p.1))) : ↥(CohCarrier.GammaH M H))))))
    (fun p => (γ₁ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') p.2) * (CohCarrier.conjL M H ℓ (sfac M H (CohCarrier.GammaHUpper M H ℓ) (γ₂ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') p.2) * (CohCarrier.conjL M H ℓ' (sfac M H (CohCarrier.GammaHUpper M H ℓ') (γ₃ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') p.2) * (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) p.1))) : ↥(CohCarrier.GammaH M H)))) : ↥(CohCarrier.GammaH M H)))⁻¹)
    (by
      rintro ⟨j, k⟩
      change alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ) (γ₂ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k) * (CohCarrier.conjL M H ℓ' (sfac M H (CohCarrier.GammaHUpper M H ℓ') (γ₃ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k) * (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) j))) : ↥(CohCarrier.GammaH M H))))) * (alpha ℓ' * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ') (γ₃ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k) * (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) j))))) =
        ιΓ M H ((γ₁ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k) * (CohCarrier.conjL M H ℓ (sfac M H (CohCarrier.GammaHUpper M H ℓ) (γ₂ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k) * (CohCarrier.conjL M H ℓ' (sfac M H (CohCarrier.GammaHUpper M H ℓ') (γ₃ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k) * (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) j))) : ↥(CohCarrier.GammaH M H)))) : ↥(CohCarrier.GammaH M H)))⁻¹) *
          (alpha ℓ' * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k) * (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) j)))
      have e1 := hγ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k)
      generalize hg3 : γ₃ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k) * (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) j) = g₃
      have hs3 := sfac_spec M H (CohCarrier.GammaHUpper M H ℓ') g₃
      generalize hs3d : sfac M H (CohCarrier.GammaHUpper M H ℓ') g₃ = s₃ at hs3 ⊢
      have hιg3 : ιΓ M H g₃ = ιΓ M H (s₃ : ↥(CohCarrier.GammaH M H)) * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ') g₃)) := by
        rw [← map_mul, hs3]
      generalize hg2 : γ₂ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k) * (CohCarrier.conjL M H ℓ' s₃ : ↥(CohCarrier.GammaH M H)) = g₂
      have hs2 := sfac_spec M H (CohCarrier.GammaHUpper M H ℓ) g₂
      generalize hs2d : sfac M H (CohCarrier.GammaHUpper M H ℓ) g₂ = s₂ at hs2 ⊢
      have hιg2 : ιΓ M H g₂ = ιΓ M H (s₂ : ↥(CohCarrier.GammaH M H)) * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ) g₂)) := by
        rw [← map_mul, hs2]
      have chain : alpha ℓ' * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k) * (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) j)) =
          ιΓ M H (γ₁ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k) * (CohCarrier.conjL M H ℓ s₂ : ↥(CohCarrier.GammaH M H))) *
            (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ) g₂)) *
              (alpha ℓ' * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ') g₃)))) := by
        calc alpha ℓ' * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k) * (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) j))
            = alpha ℓ' * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k) * alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) j) := by simp only [mul_assoc]
          _ = ιΓ M H (γ₁ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k)) * alpha ℓ * ιΓ M H (γ₂ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k)) * alpha ℓ' * ιΓ M H (γ₃ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k)) *
                ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) j) := by rw [e1]
          _ = ιΓ M H (γ₁ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k)) * alpha ℓ * ιΓ M H (γ₂ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k)) * alpha ℓ' * ιΓ M H g₃ := by
                rw [mul_assoc _ (ιΓ M H (γ₃ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k))) _, ← map_mul, hg3]
          _ = ιΓ M H (γ₁ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k)) * alpha ℓ * ιΓ M H (γ₂ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k)) *
                (alpha ℓ' * ιΓ M H (s₃ : ↥(CohCarrier.GammaH M H))) *
                ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ') g₃)) := by rw [hιg3]; simp only [mul_assoc]
          _ = ιΓ M H (γ₁ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k)) * alpha ℓ * ιΓ M H (γ₂ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k)) *
                (ιΓ M H (CohCarrier.conjL M H ℓ' s₃ : ↥(CohCarrier.GammaH M H)) * alpha ℓ') *
                ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ') g₃)) := by rw [alpha_mul_ιΓ]
          _ = ιΓ M H (γ₁ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k)) * alpha ℓ * ιΓ M H g₂ * alpha ℓ' *
                ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ') g₃)) := by rw [← hg2, map_mul]; simp only [mul_assoc]
          _ = ιΓ M H (γ₁ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k)) * (alpha ℓ * ιΓ M H (s₂ : ↥(CohCarrier.GammaH M H))) *
                ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ) g₂)) * alpha ℓ' *
                ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ') g₃)) := by rw [hιg2]; simp only [mul_assoc]
          _ = ιΓ M H (γ₁ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k)) * (ιΓ M H (CohCarrier.conjL M H ℓ s₂ : ↥(CohCarrier.GammaH M H)) * alpha ℓ) *
                ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ) g₂)) * alpha ℓ' *
                ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ') g₃)) := by rw [alpha_mul_ιΓ]
          _ = ιΓ M H (γ₁ (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') k) * (CohCarrier.conjL M H ℓ s₂ : ↥(CohCarrier.GammaH M H))) *
                (alpha ℓ * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ) (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ) g₂)) *
                  (alpha ℓ' * ιΓ M H (CohCarrier.rep (CohCarrier.GammaHUpper M H ℓ') (CohCarrier.cls (CohCarrier.GammaHUpper M H ℓ') g₃)))) := by
                rw [map_mul]; simp only [mul_assoc]
      rw [map_inv, chain, inv_mul_cancel_left])
  exact ⟨π, ε, hε⟩

end CC3b
p2m_reactivate "P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm.HeckeFamily P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm"

section CC3bPrime

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ ℓ' : ℕ) [NeZero ℓ] [NeZero ℓ']

def pMat (x w : ℤ) : SL(2, ℤ) :=
  ⟨!![1, x; w, w * x + 1], by rw [Matrix.det_fin_two_of]; ring⟩

@[scoped simp] theorem pMat_00 (x w : ℤ) : (pMat x w : SL(2, ℤ)) 0 0 = 1 := rfl
@[scoped simp] theorem pMat_01 (x w : ℤ) : (pMat x w : SL(2, ℤ)) 0 1 = x := rfl
@[scoped simp] theorem pMat_10 (x w : ℤ) : (pMat x w : SL(2, ℤ)) 1 0 = w := rfl
@[scoped simp] theorem pMat_11 (x w : ℤ) : (pMat x w : SL(2, ℤ)) 1 1 = w * x + 1 := rfl

omit [NeZero ℓ] [NeZero ℓ'] in
theorem pMat_mem (x w : ℤ) (hw : (M : ℤ) ∣ w) : pMat x w ∈ CohCarrier.GammaH M H := by
  have hw0 : (w : ZMod M) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd w M).mpr hw
  have h0 : pMat x w ∈ Gamma0 M := by
    rw [Gamma0_mem]
    show ((w : ℤ) : ZMod M) = 0
    exact hw0
  refine CohCarrier.mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have e : CohCarrier.gamma0Units M ⟨pMat x w, h0⟩ = 1 := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, Units.val_one]
    show ((w * x + 1 : ℤ) : ZMod M) = 1
    push_cast
    rw [hw0, zero_mul, zero_add]
  rw [e]
  exact H.one_mem

def zMat (A B e f : ℤ) (l : ℤ) (h : A * f - l * B * e = 1) : SL(2, ℤ) :=
  ⟨!![A, l * B; e, f], by rw [Matrix.det_fin_two_of]; exact h⟩

@[scoped simp] theorem zMat_00 (A B e f l : ℤ) (h) : (zMat A B e f l h : SL(2, ℤ)) 0 0 = A := rfl
@[scoped simp] theorem zMat_01 (A B e f l : ℤ) (h) : (zMat A B e f l h : SL(2, ℤ)) 0 1 = l * B := rfl
@[scoped simp] theorem zMat_10 (A B e f l : ℤ) (h) : (zMat A B e f l h : SL(2, ℤ)) 1 0 = e := rfl
@[scoped simp] theorem zMat_11 (A B e f l : ℤ) (h) : (zMat A B e f l h : SL(2, ℤ)) 1 1 = f := rfl

omit [NeZero ℓ] [NeZero ℓ'] in

theorem mem_GammaH_of_entries (g : ↥(CohCarrier.GammaH M H)) (Z : SL(2, ℤ)) (h10 : (M : ℤ) ∣ Z 1 0)
    (h11 : ((Z 1 1 : ℤ) : ZMod M) = (((g : SL(2, ℤ)) 1 1 : ℤ) : ZMod M)) : Z ∈ CohCarrier.GammaH M H := by
  obtain ⟨hg0, hgH⟩ := CohCarrier.mem_GammaH_iff.mp g.2
  have h0 : Z ∈ Gamma0 M := by
    rw [Gamma0_mem]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mpr h10
  refine CohCarrier.mem_GammaH_iff.mpr ⟨h0, ?_⟩
  have e : CohCarrier.gamma0Units M ⟨Z, h0⟩ = CohCarrier.gamma0Units M ⟨(g : SL(2, ℤ)), hg0⟩ := by
    apply Units.ext
    rw [CohCarrier.val_gamma0Units, CohCarrier.val_gamma0Units]
    exact h11
  rw [e]
  exact hgH

omit [NeZero ℓ] [NeZero ℓ'] in
theorem isCoprime_of_prime_not_dvd (hℓ : ℓ.Prime) {A : ℤ} (h : ¬ (ℓ : ℤ) ∣ A) : IsCoprime A (ℓ : ℤ) := by
  have h1 : Nat.Coprime ℓ A.natAbs := (Nat.Prime.coprime_iff_not_dvd hℓ).mpr (fun h' => h (Int.natCast_dvd.mpr h'))
  have h2 : IsCoprime (ℓ : ℤ) (A.natAbs : ℤ) := Nat.isCoprime_iff_coprime.mpr h1
  rcases Int.natAbs_eq A with hA | hA
  · rw [← hA] at h2
    exact h2.symm
  · have h3 := h2.neg_right
    rw [← hA] at h3
    exact h3.symm

theorem twoSidedReduction_of_prime (hℓ : ℓ.Prime) (hcop : Nat.Coprime ℓ ℓ') : TwoSidedReduction M H ℓ ℓ' := by
  intro g
  have hdet : (g : SL(2, ℤ)) 0 0 * (g : SL(2, ℤ)) 1 1 - (g : SL(2, ℤ)) 0 1 * (g : SL(2, ℤ)) 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe (g : SL(2, ℤ))
    rwa [Matrix.det_fin_two] at h
  obtain ⟨hg0, -⟩ := CohCarrier.mem_GammaH_iff.mp g.2
  obtain ⟨c', hc'⟩ : (M : ℤ) ∣ (g : SL(2, ℤ)) 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ M).mp (Gamma0_mem.mp hg0)
  have hℓZ : _root_.Prime (ℓ : ℤ) := Nat.prime_iff_prime_int.mp hℓ
  obtain ⟨x, hx⟩ : ∃ x : ℤ, ¬ (ℓ : ℤ) ∣ ((g : SL(2, ℤ)) 0 0 + x * ℓ' * (g : SL(2, ℤ)) 1 0) := by
    by_cases ha : (ℓ : ℤ) ∣ (g : SL(2, ℤ)) 0 0
    · refine ⟨1, fun h1 => ?_⟩
      have h2 : (ℓ : ℤ) ∣ (ℓ' : ℤ) * (g : SL(2, ℤ)) 1 0 := by
        have h3 := dvd_sub h1 ha
        rwa [one_mul, add_sub_cancel_left] at h3
      rcases hℓZ.dvd_or_dvd h2 with h3 | h3
      · exact (Nat.Prime.coprime_iff_not_dvd hℓ).mp hcop (Int.natCast_dvd_natCast.mp h3)
      · have h4 : (ℓ : ℤ) ∣ 1 := by
          rw [← hdet]
          exact dvd_sub (dvd_mul_of_dvd_left ha _) (dvd_mul_of_dvd_right h3 _)
        exact hℓZ.not_unit (isUnit_of_dvd_one h4)
    · exact ⟨0, by rwa [zero_mul, zero_mul, add_zero]⟩
  obtain ⟨m, n, hmn⟩ := isCoprime_of_prime_not_dvd ℓ hℓ hx

  have hZ : ((g : SL(2, ℤ)) 0 0 + x * ℓ' * (g : SL(2, ℤ)) 1 0) *
        (M * -(c' * m) * ((g : SL(2, ℤ)) 0 1 + x * ℓ' * (g : SL(2, ℤ)) 1 1) + (g : SL(2, ℤ)) 1 1) -
      ℓ * ((g : SL(2, ℤ)) 0 1 + x * ℓ' * (g : SL(2, ℤ)) 1 1) * (M * (c' * n)) = 1 := by
    linear_combination hdet + ((g : SL(2, ℤ)) 0 1 + x * ℓ' * (g : SL(2, ℤ)) 1 1) * hc' -
      M * c' * ((g : SL(2, ℤ)) 0 1 + x * ℓ' * (g : SL(2, ℤ)) 1 1) * hmn
  have hw : (M : ℤ) ∣ M * ℓ' * -(c' * m) := ⟨ℓ' * -(c' * m), by ring⟩
  refine ⟨(⟨pMat x (M * ℓ' * -(c' * m)), pMat_mem M H x _ hw⟩ : ↥(CohCarrier.GammaH M H))⁻¹, 1,
    ⟨zMat _ _ (M * (c' * n)) _ ℓ hZ, mem_GammaH_of_entries M H g _ ⟨c' * n, rfl⟩ (by
      show ((M * -(c' * m) * ((g : SL(2, ℤ)) 0 1 + x * ℓ' * (g : SL(2, ℤ)) 1 1) + (g : SL(2, ℤ)) 1 1 : ℤ) : ZMod M) = _
      push_cast
      rw [ZMod.natCast_self, zero_mul, zero_mul, zero_add])⟩, ?_⟩

  have hcQ : ((((g : SL(2, ℤ)) 1 0 : ℤ)) : ℚ) = (M : ℚ) * (c' : ℚ) := by exact_mod_cast hc'
  have hmnQ : (m : ℚ) * ((((g : SL(2, ℤ)) 0 0 : ℤ) : ℚ) + (x : ℚ) * (ℓ' : ℚ) * ((((g : SL(2, ℤ)) 1 0 : ℤ)) : ℚ)) +
      (n : ℚ) * (ℓ : ℚ) = 1 := by exact_mod_cast hmn
  have H2 : (ℓ' : ℚ) * ((((g : SL(2, ℤ)) 1 0 : ℤ)) : ℚ) = (ℓ' : ℚ) * ((M : ℚ) * (c' : ℚ)) := by rw [hcQ]
  have H3 : (M : ℚ) * c' * ℓ' * ((m : ℚ) * ((((g : SL(2, ℤ)) 0 0 : ℤ) : ℚ) + (x : ℚ) * (ℓ' : ℚ) *
      ((((g : SL(2, ℤ)) 1 0 : ℤ)) : ℚ)) + (n : ℚ) * (ℓ : ℚ)) = (M : ℚ) * c' * ℓ' := by rw [hmnQ, mul_one]
  have key : ιQ (pMat x (M * ℓ' * -(c' * m))) * (alpha ℓ' * ιΓ M H g * alpha ℓ) =
      alpha ℓ * alpha ℓ' * ιQ (zMat _ _ (M * (c' * n)) _ ℓ hZ) := by
    apply Matrix.GeneralLinearGroup.ext
    intro i j
    simp only [Matrix.GeneralLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, alpha_coe, ιQ_coe_apply, ιΓ_coe_apply]
    fin_cases i <;> fin_cases j
    · simp
      ring
    · simp
      ring
    · simp
      linarith [H2, H3]
    · simp
      ring
  have key' : (ιQ (pMat x (M * ℓ' * -(c' * m))))⁻¹ * alpha ℓ * alpha ℓ' * ιQ (zMat _ _ (M * (c' * n)) _ ℓ hZ) =
      alpha ℓ' * ιΓ M H g * alpha ℓ := by
    rw [mul_assoc (ιQ (pMat x (M * ℓ' * -(c' * m))))⁻¹, mul_assoc (ιQ (pMat x (M * ℓ' * -(c' * m))))⁻¹, ← key,
      inv_mul_cancel_left]
  rw [map_one, mul_one, map_inv]
  exact key'.symm

theorem commPrime_impl (hℓ : ℓ.Prime) (hcop : Nat.Coprime ℓ ℓ') (V : Type) [AddCommGroup V]
    (F : Additive ↥(CohCarrier.GammaH M H) →+ V) :
    CohCarrier.heckeT M H ℓ V (CohCarrier.heckeT M H ℓ' V F) =
      CohCarrier.heckeT M H ℓ' V (CohCarrier.heckeT M H ℓ V F) :=
  heckeT_comm_of_sameCosetsComm M H ℓ ℓ'
    (sameCosetsComm_of_twoSided M H ℓ ℓ' hcop (twoSidedReduction_of_prime M H ℓ ℓ' hℓ hcop)) V F

end CC3bPrime
p2m_reactivate "P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm.HeckeFamily P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm"

section DiamondDiamond

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ)

theorem diamondRaw_diamondRaw (σ σ' : Gamma0 M) (V : Type) [AddCommGroup V]
    (F : Additive ↥(CohCarrier.GammaH M H) →+ V) :
    CohCarrier.diamondRaw M H V σ (CohCarrier.diamondRaw M H V σ' F) = CohCarrier.diamondRaw M H V (σ' * σ) F := by
  refine AddMonoidHom.ext fun g => ?_
  show F (Additive.ofMul (CohCarrier.conjHom M H σ' (CohCarrier.conjHom M H σ g.toMul))) =
    F (Additive.ofMul (CohCarrier.conjHom M H (σ' * σ) g.toMul))
  congr 2
  apply Subtype.ext
  show (σ' : SL(2, ℤ)) * ((σ : SL(2, ℤ)) * (g.toMul : SL(2, ℤ)) * (σ : SL(2, ℤ))⁻¹) * (σ' : SL(2, ℤ))⁻¹ =
    ((σ' * σ : Gamma0 M) : SL(2, ℤ)) * (g.toMul : SL(2, ℤ)) * ((σ' * σ : Gamma0 M) : SL(2, ℤ))⁻¹
  rw [Subgroup.coe_mul]
  group

theorem commutator_mem_GammaH (σ σ' : Gamma0 M) :
    ((σ * σ' : Gamma0 M) : SL(2, ℤ)) * ((σ' * σ : Gamma0 M) : SL(2, ℤ))⁻¹ ∈ CohCarrier.GammaH M H := by
  refine CohCarrier.mem_GammaH_iff.mpr ⟨(σ * σ' * (σ' * σ)⁻¹).2, ?_⟩
  have e : CohCarrier.gamma0Units M ⟨((σ * σ' : Gamma0 M) : SL(2, ℤ)) * ((σ' * σ : Gamma0 M) : SL(2, ℤ))⁻¹,
      (σ * σ' * (σ' * σ)⁻¹).2⟩ = CohCarrier.gamma0Units M (σ * σ' * (σ' * σ)⁻¹) := rfl
  rw [e, map_mul, map_inv, map_mul, map_mul, mul_comm (CohCarrier.gamma0Units M σ') (CohCarrier.gamma0Units M σ),
    mul_inv_cancel]
  exact H.one_mem

theorem twoDiamonds_impl (σ σ' : Gamma0 M) (V : Type) [AddCommGroup V] (F : Additive ↥(CohCarrier.GammaH M H) →+ V) :
    CohCarrier.diamondRaw M H V σ (CohCarrier.diamondRaw M H V σ' F) =
      CohCarrier.diamondRaw M H V σ' (CohCarrier.diamondRaw M H V σ F) := by
  rw [diamondRaw_diamondRaw, diamondRaw_diamondRaw]
  exact diamondRaw_congr M H (σ * σ') (σ' * σ) (commutator_mem_GammaH M H σ' σ) V F

end DiamondDiamond
p2m_reactivate "P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm.HeckeFamily P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm"

end IharaSolComm
p2m_reactivate "P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm.HeckeFamily P2MW.S_CohCarrier_diamondRaw_comm.IharaSolComm"

open CohCarrier in
theorem solution (M : ℕ) (H : Subgroup (ZMod M)ˣ) (σ σ' : CongruenceSubgroup.Gamma0 M)
    {V : Type} [AddCommGroup V] (F : H1 M H V) :
    diamondRaw M H V σ (diamondRaw M H V σ' F) = diamondRaw M H V σ' (diamondRaw M H V σ F) :=
  IharaSolComm.twoDiamonds_impl M H σ σ' V F

#print axioms solution

end S_CohCarrier_diamondRaw_comm
end P2MW
export P2MW.S_CohCarrier_diamondRaw_comm (solution)
