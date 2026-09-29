-- Prove2me | solution 1 for CohCarrier.heckeSym_top
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/6764cb41-1d8e-526f-80fc-5c1909dd12bf

import Definitions.Def_CohCarrier_Lower
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CohCarrier_heckeSym_top

set_option autoImplicit false
attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

namespace IharaMintRQ

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

theorem heckeTlower_apply_eq_sum_rq (M : ℕ) (H : Subgroup (ZMod M)ˣ) (q : ℕ)
    [NeZero M] [NeZero q] {V : Type} [AddCommGroup V]
    (F : Additive ↥(GammaH M H) →+ V) (γ : ↥(GammaH M H)) :
    heckeTlower M H q V F (Additive.ofMul γ) =
      ∑ r : Quotient (QuotientGroup.rightRel (GammaHLower M H q)),
        F (Additive.ofMul (conjLowerL M H q (slip (GammaHLower M H q) r γ))) :=
  toAdditiveLeft_transfer_apply (GammaHLower M H q)
    ((AddMonoidHom.toMultiplicativeRight F).comp (conjLowerL M H q)) γ

end IharaMintRQ

namespace IharaMintHS

open CohCarrier IharaMintRQ CongruenceSubgroup
open scoped MatrixGroups

variable (M q : ℕ) [NeZero M] [NeZero q]

omit [NeZero M] [NeZero q] in
theorem repcls_mul_inv_mem (S : Subgroup ↥(GammaH M ⊤)) (x : ↥(GammaH M ⊤)) :
    rep S (cls S x) * x⁻¹ ∈ S := by
  have h : QuotientGroup.rightRel S (rep S (cls S x)) x :=
    Quotient.exact' (by simp [rep, cls])
  rw [QuotientGroup.rightRel_apply] at h
  simpa only [_root_.mul_inv_rev, inv_inv] using S.inv_mem h

variable (hcop : Nat.Coprime q M) (u v : ℤ) (hBez : (q : ℤ) * u + (M : ℤ) * v = 1)

def flipQSL : SL(2, ℤ) :=
  ⟨!![1, -v; (M : ℤ), (q : ℤ) * u], by rw [Matrix.det_fin_two_of]; linarith [hBez]⟩

noncomputable def flipQ : ↥(GammaH M ⊤) :=
  ⟨flipQSL M q u v hBez, by rw [GammaH_top]; exact Gamma0_mem.mpr (by simp [flipQSL])⟩

def flipPSL : SL(2, ℤ) :=
  ⟨!![(q : ℤ), -v; (M : ℤ), u], by rw [Matrix.det_fin_two_of]; linarith [hBez]⟩

noncomputable def flipP : ↥(GammaH M ⊤) :=
  ⟨flipPSL M q u v hBez, by rw [GammaH_top]; exact Gamma0_mem.mpr (by simp [flipPSL])⟩

omit [NeZero M] [NeZero q] in
theorem eQm : ((flipQ M q u v hBez : ↥(GammaH M ⊤)) : SL(2, ℤ))
    = (!![1, -v; (M : ℤ), (q : ℤ) * u] : Matrix (Fin 2) (Fin 2) ℤ) := rfl

omit [NeZero M] [NeZero q] in
theorem hconjLow (s : ↥(GammaHLower M ⊤ q)) :
    (flipQ M q u v hBez)⁻¹ * (s : ↥(GammaH M ⊤)) * (flipQ M q u v hBez)
      ∈ GammaHUpper M ⊤ q := by
  have hs10 : (((s : ↥(GammaH M ⊤)) : SL(2, ℤ)) 1 0 : ZMod q) = 0 := by
    have := dvd_of_mem_GammaHLower M ⊤ q s
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr this
  rw [Subgroup.mem_subgroupOf, mem_Gamma0Upper]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, eQm, Matrix.adjugate_fin_two_of]
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  rw [hs10, ZMod.natCast_self]
  ring

omit [NeZero M] [NeZero q] in
include hcop in
theorem hconjUp (s : ↥(GammaHUpper M ⊤ q)) :
    (flipQ M q u v hBez) * (s : ↥(GammaH M ⊤)) * (flipQ M q u v hBez)⁻¹
      ∈ GammaHLower M ⊤ q := by
  have hs01 : (((s : ↥(GammaH M ⊤)) : SL(2, ℤ)) 0 1 : ZMod q) = 0 := by
    have := dvd_of_mem_GammaHUpper M ⊤ q s
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr this
  rw [mem_GammaHLower_iff_of_coprime M ⊤ q hcop, ← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Matrix.SpecialLinearGroup.coe_mul,
    Matrix.SpecialLinearGroup.coe_inv, eQm, Matrix.adjugate_fin_two_of]
  rw [Matrix.mul_apply, Fin.sum_univ_two, Matrix.mul_apply, Matrix.mul_apply, Fin.sum_univ_two,
    Fin.sum_univ_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  push_cast
  rw [hs01, ZMod.natCast_self]
  ring

omit [NeZero M] [NeZero q] in
include hcop in

theorem πUL_mk (y : ↥(GammaH M ⊤)) :
    (Quotient.mk'' ((flipQ M q u v hBez) * y)
        : Quotient (QuotientGroup.rightRel (GammaHLower M ⊤ q)))
      = cls (GammaHLower M ⊤ q)
          ((flipQ M q u v hBez) * rep (GammaHUpper M ⊤ q) (Quotient.mk'' y)) := by
  apply Quotient.sound'
  rw [QuotientGroup.rightRel_apply]
  have hs := repcls_mul_inv_mem M (GammaHUpper M ⊤ q) y
  have heq : (flipQ M q u v hBez) * rep (GammaHUpper M ⊤ q) (cls (GammaHUpper M ⊤ q) y)
      * ((flipQ M q u v hBez) * y)⁻¹
      = (flipQ M q u v hBez) * (rep (GammaHUpper M ⊤ q) (cls (GammaHUpper M ⊤ q) y) * y⁻¹)
          * (flipQ M q u v hBez)⁻¹ := by group
  show (flipQ M q u v hBez) * rep (GammaHUpper M ⊤ q) (Quotient.mk'' y)
      * ((flipQ M q u v hBez) * y)⁻¹ ∈ _
  rw [heq]
  exact hconjUp M q hcop u v hBez ⟨_, hs⟩

noncomputable def πUL :
    Quotient (QuotientGroup.rightRel (GammaHUpper M ⊤ q)) ≃
      Quotient (QuotientGroup.rightRel (GammaHLower M ⊤ q)) where
  toFun k := cls _ ((flipQ M q u v hBez) * rep _ k)
  invFun r := cls _ ((flipQ M q u v hBez)⁻¹ * rep _ r)
  left_inv k := by
    set x := (flipQ M q u v hBez) * rep (GammaHUpper M ⊤ q) k with hx
    have hs := repcls_mul_inv_mem M (GammaHLower M ⊤ q) x
    set s := rep (GammaHLower M ⊤ q) (cls (GammaHLower M ⊤ q) x) * x⁻¹ with hsdef
    have hmem : rep (GammaHUpper M ⊤ q) k *
        ((flipQ M q u v hBez)⁻¹ * rep (GammaHLower M ⊤ q)
          (cls (GammaHLower M ⊤ q) x))⁻¹ ∈ GammaHUpper M ⊤ q := by
      have heq : rep (GammaHUpper M ⊤ q) k *
          ((flipQ M q u v hBez)⁻¹ * rep (GammaHLower M ⊤ q)
            (cls (GammaHLower M ⊤ q) x))⁻¹
          = (flipQ M q u v hBez)⁻¹ * s⁻¹ * (flipQ M q u v hBez) := by
        rw [show rep (GammaHLower M ⊤ q) (cls (GammaHLower M ⊤ q) x) = s * x from by
          rw [hsdef]; group, hx]
        group
      rw [heq, show (flipQ M q u v hBez)⁻¹ * s⁻¹ * (flipQ M q u v hBez)
          = ((flipQ M q u v hBez)⁻¹ * s * (flipQ M q u v hBez))⁻¹ from by group]
      exact (GammaHUpper M ⊤ q).inv_mem (hconjLow M q u v hBez ⟨s, hs⟩)
    exact (Quotient.sound' (QuotientGroup.rightRel_apply.mpr hmem)).trans (Quotient.out_eq' k)
  right_inv r := by
    set x := (flipQ M q u v hBez)⁻¹ * rep (GammaHLower M ⊤ q) r with hx
    have hs := repcls_mul_inv_mem M (GammaHUpper M ⊤ q) x
    set s := rep (GammaHUpper M ⊤ q) (cls (GammaHUpper M ⊤ q) x) * x⁻¹ with hsdef
    have hmem : rep (GammaHLower M ⊤ q) r *
        ((flipQ M q u v hBez) * rep (GammaHUpper M ⊤ q)
          (cls (GammaHUpper M ⊤ q) x))⁻¹ ∈ GammaHLower M ⊤ q := by
      have heq : rep (GammaHLower M ⊤ q) r *
          ((flipQ M q u v hBez) * rep (GammaHUpper M ⊤ q)
            (cls (GammaHUpper M ⊤ q) x))⁻¹
          = (flipQ M q u v hBez) * s⁻¹ * (flipQ M q u v hBez)⁻¹ := by
        rw [show rep (GammaHUpper M ⊤ q) (cls (GammaHUpper M ⊤ q) x) = s * x from by
          rw [hsdef]; group, hx]
        group
      rw [heq, show (flipQ M q u v hBez) * s⁻¹ * (flipQ M q u v hBez)⁻¹
          = ((flipQ M q u v hBez) * s * (flipQ M q u v hBez)⁻¹)⁻¹ from by group]
      exact (GammaHLower M ⊤ q).inv_mem (hconjUp M q hcop u v hBez ⟨s, hs⟩)
    exact (Quotient.sound' (QuotientGroup.rightRel_apply.mpr hmem)).trans (Quotient.out_eq' r)

omit [NeZero M] [NeZero q] in
theorem πUL_mk' (y : ↥(GammaH M ⊤)) :
    πUL M q hcop u v hBez (Quotient.mk'' y) = Quotient.mk'' ((flipQ M q u v hBez) * y) :=
  (πUL_mk M q hcop u v hBez y).symm

set_option maxHeartbeats 1600000 in
omit [NeZero M] in

theorem conjLowerMat_flipQ_conj_eq (X : SL(2, ℤ)) (hX : (q : ℤ) ∣ X 0 1)
    (h10 : (q : ℤ) ∣ (flipQSL M q u v hBez * X * (flipQSL M q u v hBez)⁻¹ : SL(2, ℤ)) 1 0) :
    conjLowerMat q (flipQSL M q u v hBez * X * (flipQSL M q u v hBez)⁻¹) h10
      = flipPSL M q u v hBez * conjUpperMat q X hX * (flipPSL M q u v hBez)⁻¹ := by
  have hq0 : (q : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne q)
  have ⟨b', hb'⟩ := hX
  have eQ : ((flipQSL M q u v hBez : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![1, -v; (M : ℤ), (q : ℤ) * u] := rfl
  have eQi : (((flipQSL M q u v hBez)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![(q : ℤ) * u, v; -(M : ℤ), 1] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, eQ, Matrix.adjugate_fin_two_of]; simp
  have eP : ((flipPSL M q u v hBez : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![(q : ℤ), -v; (M : ℤ), u] := rfl
  have ePi : (((flipPSL M q u v hBez)⁻¹ : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
      = !![u, v; -(M : ℤ), (q : ℤ)] := by
    rw [Matrix.SpecialLinearGroup.coe_inv, eP, Matrix.adjugate_fin_two_of]; simp
  have eL : ∀ i j : Fin 2,
      (flipQSL M q u v hBez * X * (flipQSL M q u v hBez)⁻¹ : SL(2, ℤ)) i j
      = (!![1, -v; (M : ℤ), (q : ℤ) * u] * (X : Matrix (Fin 2) (Fin 2) ℤ)
          * !![(q : ℤ) * u, v; -(M : ℤ), 1]) i j := fun i j => by
    simp only [Matrix.SpecialLinearGroup.coe_mul, eQ, eQi]
  have eR : ∀ i j : Fin 2, (flipPSL M q u v hBez * conjUpperMat q X hX
        * (flipPSL M q u v hBez)⁻¹ : SL(2, ℤ)) i j
      = (!![(q : ℤ), -v; (M : ℤ), u] * !![X 0 0, b'; X 1 0 * (q : ℤ), X 1 1]
          * !![u, v; -(M : ℤ), (q : ℤ)]) i j := fun i j => by
    have eUpm : ((conjUpperMat q X hX : SL(2, ℤ)) : Matrix (Fin 2) (Fin 2) ℤ)
        = !![X 0 0, b'; X 1 0 * (q : ℤ), X 1 1] := by
      show !![X 0 0, X 0 1 / (q : ℤ); X 1 0 * (q : ℤ), X 1 1] = _
      rw [hb', Int.mul_ediv_cancel_left _ hq0]
    simp only [Matrix.SpecialLinearGroup.coe_mul, eP, ePi, eUpm]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  fin_cases i <;> fin_cases j
  · show (flipQSL M q u v hBez * X * (flipQSL M q u v hBez)⁻¹ : SL(2, ℤ)) 0 0
      = (flipPSL M q u v hBez * conjUpperMat q X hX * (flipPSL M q u v hBez)⁻¹ : SL(2, ℤ)) 0 0
    rw [eL 0 0, eR 0 0]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [hb']; ring
  · show (flipQSL M q u v hBez * X * (flipQSL M q u v hBez)⁻¹ : SL(2, ℤ)) 0 1 * (q : ℤ)
      = (flipPSL M q u v hBez * conjUpperMat q X hX * (flipPSL M q u v hBez)⁻¹ : SL(2, ℤ)) 0 1
    rw [eL 0 1, eR 0 1]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [hb']; ring
  · show (flipQSL M q u v hBez * X * (flipQSL M q u v hBez)⁻¹ : SL(2, ℤ)) 1 0 / (q : ℤ)
      = (flipPSL M q u v hBez * conjUpperMat q X hX * (flipPSL M q u v hBez)⁻¹ : SL(2, ℤ)) 1 0
    rw [eL 1 0, eR 1 0]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [hb', show ((M : ℤ) * X 0 0 + (q : ℤ) * u * X 1 0) * ((q : ℤ) * u)
          + ((M : ℤ) * ((q : ℤ) * b') + (q : ℤ) * u * X 1 1) * -(M : ℤ)
        = (q : ℤ) * (((M : ℤ) * X 0 0 + u * (X 1 0 * q)) * u
            + ((M : ℤ) * b' + u * X 1 1) * -(M : ℤ)) from by ring,
      Int.mul_ediv_cancel_left _ hq0]
  · show (flipQSL M q u v hBez * X * (flipQSL M q u v hBez)⁻¹ : SL(2, ℤ)) 1 1
      = (flipPSL M q u v hBez * conjUpperMat q X hX * (flipPSL M q u v hBez)⁻¹ : SL(2, ℤ)) 1 1
    rw [eL 1 1, eR 1 1]
    simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rw [hb']; ring

omit [NeZero M] [NeZero q] in
theorem sk_mem (k : Quotient (QuotientGroup.rightRel (GammaHUpper M ⊤ q))) :
    rep (GammaHLower M ⊤ q) (πUL M q hcop u v hBez k)
        * ((flipQ M q u v hBez) * rep (GammaHUpper M ⊤ q) k)⁻¹
      ∈ GammaHLower M ⊤ q := by
  show rep (GammaHLower M ⊤ q) (cls (GammaHLower M ⊤ q)
      ((flipQ M q u v hBez) * rep (GammaHUpper M ⊤ q) k)) * _ ∈ _
  exact repcls_mul_inv_mem M (GammaHLower M ⊤ q) _

omit [NeZero M] [NeZero q] in
theorem πUL_mulRight (γ : ↥(GammaH M ⊤))
    (k : Quotient (QuotientGroup.rightRel (GammaHUpper M ⊤ q))) :
    πUL M q hcop u v hBez (mulRight (GammaHUpper M ⊤ q) γ k)
      = mulRight (GammaHLower M ⊤ q) γ (πUL M q hcop u v hBez k) := by
  induction k using Quotient.inductionOn' with
  | h y =>
    show πUL M q hcop u v hBez (Quotient.mk'' (y * γ))
      = mulRight (GammaHLower M ⊤ q) γ (πUL M q hcop u v hBez (Quotient.mk'' y))
    rw [πUL_mk' M q hcop u v hBez, πUL_mk' M q hcop u v hBez]
    show cls (GammaHLower M ⊤ q) ((flipQ M q u v hBez) * (y * γ))
      = cls (GammaHLower M ⊤ q) ((flipQ M q u v hBez) * y * γ)
    rw [mul_assoc]

end IharaMintHS

open CohCarrier IharaMintRQ IharaMintHS CongruenceSubgroup
open scoped MatrixGroups

set_option maxHeartbeats 3200000 in
theorem solution (M q : ℕ) [NeZero M] [NeZero q] (hq : q.Prime) (hqM : ¬ q ∣ M)
    {V : Type} [AddCommGroup V] (F : H1 M ⊤ V) :
    heckeTlower M ⊤ q V F = heckeT M ⊤ q V F := by
  have hcop : Nat.Coprime q M := (hq.coprime_iff_not_dvd).mpr hqM
  obtain ⟨u, v, hBez⟩ : ∃ u v : ℤ, (q : ℤ) * u + (M : ℤ) * v = 1 := by
    obtain ⟨u, v, h⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    exact ⟨u, v, by linarith [h]⟩
  refine AddMonoidHom.ext fun x => ?_
  obtain ⟨γ, rfl⟩ : ∃ γ, Additive.ofMul γ = x := ⟨Additive.toMul x, rfl⟩
  rw [heckeT_apply_eq_sum_rq M ⊤ q F γ, heckeTlower_apply_eq_sum_rq M ⊤ q F γ,
    ← (πUL M q hcop u v hBez).sum_comp
      (fun r => F (Additive.ofMul (conjLowerL M ⊤ q (slip (GammaHLower M ⊤ q) r γ))))]
  set wCorr : Quotient (QuotientGroup.rightRel (GammaHUpper M ⊤ q)) → ↥(GammaH M ⊤) :=
    fun k => conjLowerL M ⊤ q ⟨_, sk_mem M q hcop u v hBez k⟩ * flipP M q u v hBez with hwCorr
  have hdecomp : ∀ k, conjLowerL M ⊤ q
        (slip (GammaHLower M ⊤ q) (πUL M q hcop u v hBez k) γ)
      = wCorr k * conjL M ⊤ q (slip (GammaHUpper M ⊤ q) k γ)
        * (wCorr (mulRight (GammaHUpper M ⊤ q) γ k))⁻¹ := by
    intro k
    set r := πUL M q hcop u v hBez k
    set sk := rep (GammaHLower M ⊤ q) r
        * ((flipQ M q u v hBez) * rep (GammaHUpper M ⊤ q) k)⁻¹ with hskdef
    have hrepLr : rep (GammaHLower M ⊤ q) r
        = sk * ((flipQ M q u v hBez) * rep (GammaHUpper M ⊤ q) k) := by
      rw [hskdef]; group
    set k' := mulRight (GammaHUpper M ⊤ q) γ k with hk'
    set r' := πUL M q hcop u v hBez k' with hr'
    have hclsL : cls (GammaHLower M ⊤ q) (rep (GammaHLower M ⊤ q) r * γ) = r' := by
      rw [← mulRight_eq_cls_rep_mul, hr', hk', πUL_mulRight]
    set sk' := rep (GammaHLower M ⊤ q) r'
        * ((flipQ M q u v hBez) * rep (GammaHUpper M ⊤ q) k')⁻¹ with hsk'def
    have hrepLr' : rep (GammaHLower M ⊤ q) r'
        = sk' * ((flipQ M q u v hBez) * rep (GammaHUpper M ⊤ q) k') := by
      rw [hsk'def]; group
    have hclsU : cls (GammaHUpper M ⊤ q) (rep (GammaHUpper M ⊤ q) k * γ) = k' := by
      rw [hk', mulRight_eq_cls_rep_mul]
    have hslipLo : (slip (GammaHLower M ⊤ q) r γ : ↥(GammaH M ⊤))
        = sk * ((flipQ M q u v hBez) * (slip (GammaHUpper M ⊤ q) k γ : ↥(GammaH M ⊤))
            * (flipQ M q u v hBez)⁻¹) * sk'⁻¹ := by
      rw [coe_slip, coe_slip, hclsL, hrepLr', hclsU, hrepLr]
      group
    have hmemQuQ := hconjUp M q hcop u v hBez (slip (GammaHUpper M ⊤ q) k γ)
    have hslipLo' : slip (GammaHLower M ⊤ q) r γ
        = (⟨sk, sk_mem M q hcop u v hBez k⟩ : ↥(GammaHLower M ⊤ q)) * ⟨_, hmemQuQ⟩
          * (⟨sk', sk_mem M q hcop u v hBez k'⟩)⁻¹ :=
      Subtype.ext (by rw [hslipLo]; simp [Subgroup.coe_mul, mul_assoc])
    rw [hslipLo', map_mul, map_mul, map_inv]
    have hmid : conjLowerL M ⊤ q ⟨_, hmemQuQ⟩
        = (flipP M q u v hBez) * conjL M ⊤ q (slip (GammaHUpper M ⊤ q) k γ)
            * (flipP M q u v hBez)⁻¹ := by
      apply Subtype.ext
      show (conjLowerMat q (((⟨_, hmemQuQ⟩ : ↥(GammaHLower M ⊤ q)) : ↥(GammaH M ⊤)) : SL(2, ℤ))
            (dvd_of_mem_GammaHLower M ⊤ q ⟨_, hmemQuQ⟩) : SL(2, ℤ))
        = flipPSL M q u v hBez * conjUpperMat q
            (((slip (GammaHUpper M ⊤ q) k γ) : ↥(GammaH M ⊤)) : SL(2, ℤ))
            (dvd_of_mem_GammaHUpper M ⊤ q (slip (GammaHUpper M ⊤ q) k γ))
          * (flipPSL M q u v hBez)⁻¹
      have hcoe : (((⟨_, hmemQuQ⟩ : ↥(GammaHLower M ⊤ q)) : ↥(GammaH M ⊤)) : SL(2, ℤ))
          = flipQSL M q u v hBez
              * (((slip (GammaHUpper M ⊤ q) k γ) : ↥(GammaH M ⊤)) : SL(2, ℤ))
              * (flipQSL M q u v hBez)⁻¹ := by
        show (((flipQ M q u v hBez) * _ * (flipQ M q u v hBez)⁻¹
            : ↥(GammaH M ⊤)) : SL(2, ℤ)) = _
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]; rfl
      rw [← conjLowerMat_flipQ_conj_eq M q u v hBez
        (((slip (GammaHUpper M ⊤ q) k γ) : ↥(GammaH M ⊤)) : SL(2, ℤ))
        (dvd_of_mem_GammaHUpper M ⊤ q (slip (GammaHUpper M ⊤ q) k γ))
        (hcoe ▸ dvd_of_mem_GammaHLower M ⊤ q ⟨_, hmemQuQ⟩)]
      congr 1
    rw [hmid]
    have heq : wCorr k
        = conjLowerL M ⊤ q ⟨sk, sk_mem M q hcop u v hBez k⟩ * flipP M q u v hBez := rfl
    have heq' : wCorr k'
        = conjLowerL M ⊤ q ⟨sk', sk_mem M q hcop u v hBez k'⟩ * flipP M q u v hBez := rfl
    rw [heq, heq']
    group
  simp only [hdecomp, ofMul_mul, ofMul_inv, map_add, map_neg]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_neg_distrib]
  have hperm : ∑ k, F (Additive.ofMul (wCorr (mulRight (GammaHUpper M ⊤ q) γ k)))
      = ∑ k, F (Additive.ofMul (wCorr k)) :=
    Equiv.sum_comp (mulRight (GammaHUpper M ⊤ q) γ) (fun k => F (Additive.ofMul (wCorr k)))
  rw [hperm]
  abel

#print axioms solution

end S_CohCarrier_heckeSym_top
end P2MW
export P2MW.S_CohCarrier_heckeSym_top (solution)
