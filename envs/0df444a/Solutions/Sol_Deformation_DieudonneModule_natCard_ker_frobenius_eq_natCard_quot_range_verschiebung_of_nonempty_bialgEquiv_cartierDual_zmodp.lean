-- Prove2me | solution 1 for Deformation.DieudonneModule.natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_nonempty_bialgEquiv_cartierDual_zmodp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/37f3138d-5ced-57df-8291-b48699adfebc

import Mathlib
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_HopfAlgebra_CartierDualInstances
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_ModpRealization
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Theorems.Thm_Deformation_DieudonneModule_nonempty_ker_verschiebung_addEquiv_primitives
import Theorems.Thm_HopfAlgebra_finrank_primitives_cartierDual_eq_finrank_cotangentSpace
import Theorems.Thm_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import Theorems.Thm_Deformation_DieudonneModule_natCard_quot_range_frobenius_eq_natCard_of_ker_eq_map_frobenius_ker_counit_zmodp
import Theorems.Thm_HopfAlgebra_finrank_quotient_span_pow_prime_ker_counit_eq_pow_finrank_cotangent
import Theorems.Thm_CartierDual_isLocalRing_and_isLocalRing_cartierDual_of_bialgHom_surjective_univ
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_nonempty_bialgEquiv_cartierDual_zmodp
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open scoped TensorProduct

namespace RSZ

variable (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [Bialgebra (ZMod p) A] [Nontrivial A]

theorem charP_of_algebra_zmod : CharP A p := charP_of_injective_algebraMap (algebraMap (ZMod p) A).injective p

noncomputable def frobAlgHom : A →ₐ[ZMod p] A where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := mul_pow x y p
  map_zero' := zero_pow (Fact.out : p.Prime).ne_zero
  map_add' x y := by
    haveI : CharP A p := charP_of_algebra_zmod p A
    exact add_pow_char x y p
  commutes' a := by
    change (algebraMap (ZMod p) A a) ^ p = algebraMap (ZMod p) A a
    rw [← map_pow, ZMod.pow_card]

@[scoped simp] theorem frobAlgHom_apply (x : A) : frobAlgHom p A x = x ^ p := rfl

theorem map_frob_frob_apply (z : A ⊗[ZMod p] A) :
    Algebra.TensorProduct.map (frobAlgHom p A) (frobAlgHom p A) z = z ^ p := by
  haveI : Nontrivial (A ⊗[ZMod p] A) := (Algebra.TensorProduct.lmul' (S := A) (ZMod p)).toRingHom.domain_nontrivial
  haveI : CharP (A ⊗[ZMod p] A) p := charP_of_injective_algebraMap (algebraMap (ZMod p) (A ⊗[ZMod p] A)).injective p
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, zero_pow (Fact.out : p.Prime).ne_zero]
  | tmul a b => rw [Algebra.TensorProduct.map_tmul, frobAlgHom_apply, frobAlgHom_apply, Algebra.TensorProduct.tmul_pow]
  | add x y hx hy => rw [map_add, hx, hy, add_pow_char x y p]

noncomputable def frobBialgHom : A →ₐc[ZMod p] A :=
  BialgHom.ofAlgHom (frobAlgHom p A)
    (AlgHom.ext fun x => by
      rw [AlgHom.comp_apply, frobAlgHom_apply, map_pow, ZMod.pow_card])
    (AlgHom.ext fun x => by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, frobAlgHom_apply, map_frob_frob_apply, map_pow])

@[scoped simp] theorem frobBialgHom_apply (x : A) : frobBialgHom p A x = x ^ p := rfl

theorem exists_frobenius_bialgHom : ∃ Fk : A →ₐc[ZMod p] A, ∀ x : A, Fk x = x ^ p := ⟨frobBialgHom p A, fun _ => rfl⟩

section frobIdeal
variable (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A] [HopfAlgebra (ZMod p) A] [Nontrivial A]

abbrev augIdeal : Ideal A := RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A)

noncomputable abbrev frobIdeal : Ideal A := Ideal.map (frobBialgHom p A : A →ₐ[ZMod p] A) (augIdeal p A)

theorem frob_sub_algebraMap_counit_mem (x : A) :
    (x - algebraMap (ZMod p) A (Coalgebra.counit (R := ZMod p) x)) ^ p ∈ frobIdeal p A := by
  refine Ideal.mem_map_of_mem _ ?_
  change (x - algebraMap (ZMod p) A (Coalgebra.counit (R := ZMod p) x)) ∈ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A)
  rw [RingHom.mem_ker, map_sub]
  change Coalgebra.counit x - Bialgebra.counitAlgHom (ZMod p) A (algebraMap (ZMod p) A (Coalgebra.counit (R := ZMod p) x)) = 0
  rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

theorem mk_pow_eq (x : A) :
    Ideal.Quotient.mk (frobIdeal p A) (x ^ p) = algebraMap (ZMod p) (A ⧸ frobIdeal p A) (Coalgebra.counit (R := ZMod p) x) := by
  haveI : CharP A p := charP_of_algebra_zmod p A
  have hx : x = algebraMap (ZMod p) A (Coalgebra.counit (R := ZMod p) x) + (x - algebraMap (ZMod p) A (Coalgebra.counit (R := ZMod p) x)) := by
    abel
  conv_lhs => rw [hx]
  rw [add_pow_char _ _ p, map_add, (Ideal.Quotient.eq_zero_iff_mem).2 (frob_sub_algebraMap_counit_mem p A x), add_zero,
    ← map_pow, ZMod.pow_card]
  rfl

theorem mkₐ_comp_frob :
    (Ideal.Quotient.mkₐ (ZMod p) (frobIdeal p A)).comp (frobBialgHom p A : A →ₐ[ZMod p] A) =
      (Algebra.ofId (ZMod p) (A ⧸ frobIdeal p A)).comp (Bialgebra.counitAlgHom (ZMod p) A) :=
  AlgHom.ext fun x => mk_pow_eq p A x

omit [Nontrivial A] in

theorem map_ofId_counit_comul (T : Type*) [CommRing T] [Algebra (ZMod p) T] (a : A) :
    Algebra.TensorProduct.map ((Algebra.ofId (ZMod p) T).comp (Bialgebra.counitAlgHom (ZMod p) A))
        ((Algebra.ofId (ZMod p) T).comp (Bialgebra.counitAlgHom (ZMod p) A)) (Coalgebra.comul (R := ZMod p) a) =
      Coalgebra.counit (R := ZMod p) a • (1 : T ⊗[ZMod p] T) := by
  let 𝓡 := Coalgebra.Repr.arbitrary (ZMod p) a
  conv_lhs => rw [← 𝓡.eq]
  rw [map_sum]
  have h1 : ∀ i ∈ 𝓡.index,
      Algebra.TensorProduct.map ((Algebra.ofId (ZMod p) T).comp (Bialgebra.counitAlgHom (ZMod p) A))
        ((Algebra.ofId (ZMod p) T).comp (Bialgebra.counitAlgHom (ZMod p) A)) (𝓡.left i ⊗ₜ[ZMod p] 𝓡.right i) =
      (Coalgebra.counit (R := ZMod p) (𝓡.left i) * Coalgebra.counit (R := ZMod p) (𝓡.right i)) • (1 : T ⊗[ZMod p] T) := by
    intro i _
    rw [Algebra.TensorProduct.map_tmul, AlgHom.comp_apply, AlgHom.comp_apply, Algebra.ofId_apply, Algebra.ofId_apply,
      Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul_smul, Algebra.TensorProduct.one_def]
    rfl
  rw [Finset.sum_congr rfl h1, ← Finset.sum_smul]
  congr 1

  have h2 := congrArg (Coalgebra.counit (R := ZMod p) (A := A)) (Coalgebra.sum_counit_smul 𝓡)
  rw [map_sum] at h2
  simp only [map_smul, smul_eq_mul] at h2
  exact h2

theorem isHopfIdeal_frobIdeal : (frobIdeal p A).IsHopfIdeal' (ZMod p) where
  map_mkₐ_comul_eq_zero x hx := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx

      have hFa : Coalgebra.comul (R := ZMod p) ((frobBialgHom p A : A →ₐ[ZMod p] A) a) =
          Algebra.TensorProduct.map (frobBialgHom p A : A →ₐ[ZMod p] A) (frobBialgHom p A : A →ₐ[ZMod p] A)
            (Coalgebra.comul (R := ZMod p) a) :=
        (CoalgHomClass.map_comp_comul_apply (frobBialgHom p A) a).symm
      rw [hFa, ← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, mkₐ_comp_frob, map_ofId_counit_comul]
      have ha0 : Coalgebra.counit (R := ZMod p) a = 0 := by
        change a ∈ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A) at ha
        rwa [RingHom.mem_ker] at ha
      rw [ha0, zero_smul]
    | zero => rw [map_zero, map_zero]
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_eq_mul, Bialgebra.comul_mul, map_mul, hx, mul_zero]
  counit_eq_zero x hx := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      have ha0 : Coalgebra.counit (R := ZMod p) a = 0 := by
        change a ∈ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A) at ha
        rwa [RingHom.mem_ker] at ha
      change Bialgebra.counitAlgHom (ZMod p) A (a ^ p) = 0
      rw [map_pow]
      change Coalgebra.counit (R := ZMod p) a ^ p = 0
      rw [ha0, zero_pow (Fact.out : p.Prime).ne_zero]
    | zero => exact map_zero _
    | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
    | smul r x _ hx => rw [smul_eq_mul, Bialgebra.counit_mul, hx, mul_zero]
  antipode_mem x hx := by
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx

      have h1 : HopfAlgebra.antipode (ZMod p) ((frobBialgHom p A : A →ₐ[ZMod p] A) a) =
          (frobBialgHom p A : A →ₐ[ZMod p] A) (HopfAlgebra.antipode (ZMod p) a) := by
        change HopfAlgebra.antipodeAlgHom (ZMod p) A (a ^ p) = (HopfAlgebra.antipode (ZMod p) a) ^ p
        rw [map_pow]
        rfl
      rw [h1]
      refine Ideal.mem_map_of_mem _ ?_
      change HopfAlgebra.antipode (ZMod p) a ∈ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A)
      rw [RingHom.mem_ker]
      change Coalgebra.counit (R := ZMod p) (HopfAlgebra.antipode (ZMod p) a) = 0
      have ha0 : Coalgebra.counit (R := ZMod p) a = 0 := by
        change a ∈ RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A) at ha
        rwa [RingHom.mem_ker] at ha
      rw [← LinearMap.comp_apply, HopfAlgebra.counit_comp_antipode, ha0]
    | zero => rw [map_zero]; exact Ideal.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Ideal.add_mem _ hx hy
    | smul r x _ hx =>
      rw [smul_eq_mul]
      change HopfAlgebra.antipodeAlgHom (ZMod p) A (r * x) ∈ _
      rw [map_mul]
      exact Ideal.mul_mem_left _ _ hx

end frobIdeal

end RSZ
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_nonempty_bialgEquiv_cartierDual_zmodp.RSZ"

theorem natCard_ker_eq_natCard_quot_range {G : Type*} [AddCommGroup G] [Finite G] (f : G →+ G) :
    Nat.card f.ker = Nat.card (G ⧸ f.range) := by
  have h1 := f.ker.card_eq_card_quotient_mul_card_addSubgroup
  have h2 := f.range.card_eq_card_quotient_mul_card_addSubgroup
  have h3 : Nat.card (G ⧸ f.ker) = Nat.card f.range := Nat.card_congr (QuotientAddGroup.quotientKerEquivRange f).toEquiv
  have hpos : 0 < Nat.card f.range := Nat.card_pos
  rw [h3, mul_comm] at h1
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.symm.trans h2).symm |>.symm

section primTransport
universe u₁ v₁ w₁
variable {k : Type u₁} [Field k] {A : Type v₁} [CommRing A] [HopfAlgebra k A] {B : Type w₁} [CommRing B] [HopfAlgebra k B]

theorem mem_primitives_iff' (p : ℕ) [Fact p.Prime] [CharP k p] (x : A) :
    x ∈ primitives k A ↔ Coalgebra.comul (R := k) x = x ⊗ₜ[k] 1 + 1 ⊗ₜ[k] x := by
  change x ∈ LinearMap.ker _ ↔ _
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sub_apply, sub_sub, sub_eq_zero]
  rfl

theorem map_primitives_le (p : ℕ) [Fact p.Prime] [CharP k p] (e : A →ₐc[k] B) :
    (primitives k A).map (e : A →ₗ[k] B) ≤ primitives k B := by
  rintro _ ⟨x, hx, rfl⟩
  rw [SetLike.mem_coe, mem_primitives_iff' p] at hx
  rw [mem_primitives_iff' p]
  change Coalgebra.comul (R := k) (e x) = _
  rw [← CoalgHomClass.map_comp_comul_apply, hx, map_add, TensorProduct.map_tmul, TensorProduct.map_tmul]
  change e x ⊗ₜ e 1 + e 1 ⊗ₜ e x = _
  rw [map_one]
  rfl

theorem finrank_primitives_eq_of_bialgEquiv (p : ℕ) [Fact p.Prime] [CharP k p] (e : A ≃ₐc[k] B)
    [Module.Finite k A] [Module.Finite k B] :
    Module.finrank k ↥(primitives k A) = Module.finrank k ↥(primitives k B) := by
  apply le_antisymm
  · calc Module.finrank k ↥(primitives k A)
        = Module.finrank k ↥((primitives k A).map (e.toLinearEquiv : A →ₗ[k] B)) :=
          LinearEquiv.finrank_eq ((e.toLinearEquiv : A ≃ₗ[k] B).submoduleMap (primitives k A))
      _ ≤ Module.finrank k ↥(primitives k B) := Submodule.finrank_mono (map_primitives_le p (e : A →ₐc[k] B))
  · calc Module.finrank k ↥(primitives k B)
        = Module.finrank k ↥((primitives k B).map (e.symm.toLinearEquiv : B →ₗ[k] A)) :=
          LinearEquiv.finrank_eq ((e.symm.toLinearEquiv : B ≃ₗ[k] A).submoduleMap (primitives k B))
      _ ≤ Module.finrank k ↥(primitives k A) := Submodule.finrank_mono (map_primitives_le p (e.symm : B →ₐc[k] A))

end primTransport
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_nonempty_bialgEquiv_cartierDual_zmodp.RSZ"

universe v

theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : Type v) [CommRing A] [HopfAlgebra (ZMod p) A] [Coalgebra.IsCocomm (ZMod p) A]
    [Module.Finite (ZMod p) A]
    (hloc : IsLocalRing A) (hdual : IsLocalRing (CartierDual (ZMod p) A))
    (hself : Nonempty (A ≃ₐc[ZMod p] CartierDual (ZMod p) A)) :
    Nat.card (Deformation.DieudonneModule.frobenius (ZMod p) p A).ker =
      Nat.card (Deformation.DieudonneModule (ZMod p) p A ⧸
        (Deformation.DieudonneModule.verschiebung (ZMod p) p A).range) := by
  classical
  haveI : Nontrivial A := hloc.toNontrivial
  haveI : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩

  let Fk : A →ₐc[ZMod p] A := RSZ.frobBialgHom p A
  have hFk : ∀ x : A, Fk x = x ^ p := fun _ => rfl

  haveI hI : (RSZ.frobIdeal p A).IsHopfIdeal' (ZMod p) := RSZ.isHopfIdeal_frobIdeal p A
  let B : Type v := A ⧸ RSZ.frobIdeal p A
  let q : A →ₐc[ZMod p] B := HopfAlgebra.quotientBialgHom (ZMod p) (RSZ.frobIdeal p A)
  have hq : Function.Surjective q := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker (q : A →ₐ[ZMod p] B) = Ideal.map (Fk : A →ₐ[ZMod p] A) (RingHom.ker (Bialgebra.counitAlgHom (ZMod p) A)) :=
    Ideal.mk_ker

  haveI : Nontrivial B := by
    refine ⟨⟨0, 1, Ideal.Quotient.zero_ne_one_iff.2 fun h => ?_⟩⟩
    have h1 : (1 : A) ∈ RSZ.frobIdeal p A := h ▸ Submodule.mem_top
    have h2 := (hI.counit_eq_zero 1 h1)
    rw [Bialgebra.counit_one] at h2
    exact one_ne_zero h2

  have hBdual : IsLocalRing (CartierDual (ZMod p) B) :=
    (CartierDual.isLocalRing_and_isLocalRing_cartierDual_of_bialgHom_surjective_univ (ZMod p) A B q hq hloc hdual).2

  obtain ⟨L, hLrk, hLM⟩ := Deformation.DieudonneModule.exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
    (ZMod p) p A hdual
  obtain ⟨L', hL'rk, hL'M⟩ := Deformation.DieudonneModule.exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
    (ZMod p) p B hBdual
  have hp0 : (p : ℕ) ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [Nat.card_zmod] at hLM hL'M
  haveI : Finite (Deformation.DieudonneModule (ZMod p) p A) := Nat.finite_of_card_ne_zero (by rw [hLM]; exact pow_ne_zero _ hp0)

  obtain ⟨eV⟩ := Deformation.DieudonneModule.nonempty_ker_verschiebung_addEquiv_primitives (ZMod p) p A
  have hkerV : Nat.card (Deformation.DieudonneModule.verschiebung (ZMod p) p A).ker =
      p ^ Module.finrank (ZMod p) (cotangentSpace (ZMod p) A) := by
    rw [Nat.card_congr eV.toEquiv, Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod,
      finrank_primitives_eq_of_bialgEquiv p hself.some,
      HopfAlgebra.finrank_primitives_cartierDual_eq_finrank_cotangentSpace (ZMod p) A]

  have hcokerF : Nat.card (Deformation.DieudonneModule (ZMod p) p A ⧸ (Deformation.DieudonneModule.frobenius (ZMod p) p A).range) =
      p ^ Module.finrank (ZMod p) (cotangentSpace (ZMod p) A) := by
    rw [Deformation.DieudonneModule.natCard_quot_range_frobenius_eq_natCard_of_ker_eq_map_frobenius_ker_counit_zmodp
      p A hdual Fk hFk B q hq hker, hL'M]

    have hrk : Module.finrank (ZMod p) B = p ^ Module.finrank (ZMod p) (cotangentSpace (ZMod p) A) :=
      HopfAlgebra.finrank_quotient_span_pow_prime_ker_counit_eq_pow_finrank_cotangent p A
    rw [hL'rk] at hrk
    rw [Nat.pow_right_injective (Fact.out : p.Prime).two_le hrk]

  rw [natCard_ker_eq_natCard_quot_range, hcokerF, ← hkerV, natCard_ker_eq_natCard_quot_range]

end S_Deformation_DieudonneModule_natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_nonempty_bialgEquiv_cartierDual_zmodp
end P2MW
export P2MW.S_Deformation_DieudonneModule_natCard_ker_frobenius_eq_natCard_quot_range_verschiebung_of_nonempty_bialgEquiv_cartierDual_zmodp (solution)
