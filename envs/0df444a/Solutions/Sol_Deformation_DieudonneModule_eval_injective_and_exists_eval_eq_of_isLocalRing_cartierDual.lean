-- Prove2me | solution 1 for Deformation.DieudonneModule.eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/dd36285a-dd80-5016-ac27-2d16d961ab5a

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_Dieudonne_FontaineHodge
import Definitions.Def_Dieudonne_UnipotentWittCovector
import Definitions.Def_HopfAlgebra_CartierDual
import Definitions.Def_Dieudonne_WittGroupHopf
import Definitions.Def_HopfAlgebra_HopfIdealQuotient
import Theorems.Thm_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_DieudonneModule_exists_map_eq_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_DieudonneModule_finrank_adjoin_coeff_le_natCard
import Theorems.Thm_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra HopfAlgebra.IsHopfTower.refl CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply"

set_option autoImplicit false

open Function
open scoped TensorProduct

universe u v w

namespace DieudonnePoints

open Deformation Deformation.DieudonneModule

section General

variable {R : Type u} [CommRing R] {p : ℕ} [hp : Fact p.Prime]
variable {C : Type v} [CommRing C] [Bialgebra R C]

theorem verschiebung_iterate_of {n : ℕ} (x : wittHom R p n C) (k : ℕ) :
    (verschiebung R p C)^[k] (of R p C n x) = of R p C n ((wittHomVerschiebung R p n C)^[k] x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [iterate_succ_apply', ih, verschiebung_of]
    exact congrArg (of R p C n) (iterate_succ_apply' (wittHomVerschiebung R p n C) k x).symm

theorem verschiebung_iterate_of_self {n : ℕ} (x : wittHom R p n C) :
    (verschiebung R p C)^[n] (of R p C n x) = 0 := by
  rw [verschiebung_iterate_of, wittHomVerschiebung_iterate_eq_zero, map_zero]

theorem exists_level [Finite (DieudonneModule R p C)] :
    ∃ N : ℕ, ∀ z : DieudonneModule R p C, ∃ x : wittHom R p N C, of R p C N x = z := by
  haveI : Fintype (DieudonneModule R p C) := Fintype.ofFinite _
  choose n x hx using fun z : DieudonneModule R p C => exists_of z
  refine ⟨Finset.univ.sup n, fun z => ?_⟩
  have hz : n z ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ z)
  exact ⟨wittHomShiftLE R p C hz (x z), by rw [of_shiftLE, hx]⟩

end General

section Injective

variable (p : ℕ) [Fact p.Prime]
variable {B : Type u} [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
  [Module.Finite (ZMod p) B]
variable {S : Type v} [CommRing S] [Algebra (ZMod p) S]

theorem eval_injective (hB : IsLocalRing (CartierDual (ZMod p) B)) {f g : B →ₐ[ZMod p] S}
    (h : DieudonneModule.eval (ZMod p) p f = DieudonneModule.eval (ZMod p) p g) : f = g := by
  refine AlgHom.ext_of_adjoin_eq_top
    (adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual (ZMod p) p B hB) ?_
  rintro b ⟨n, x, i, rfl⟩
  have hx := DFunLike.congr_fun h (DieudonneModule.of (ZMod p) p B n x)
  rw [DieudonneModule.eval_of, DieudonneModule.eval_of] at hx
  have hx' := congrArg (TruncatedWittVector.coeff i) (UnipotentWittCovector.of_injective n hx)
  simp only [TruncWitt.coeff_map] at hx'
  exact hx'

end Injective

section Envelope

variable (p : ℕ) [hp : Fact p.Prime]
variable (B : Type u) [CommRing B] [HopfAlgebra (ZMod p) B]
variable (N : ℕ)

abbrev M : Type u := DieudonneModule (ZMod p) p B

abbrev C : Type u := WittGroup.Coord (ZMod p) p N (M p B)

noncomputable abbrev u (z : M p B) : TruncatedWittVector p N (C p B N) := WittGroup.univ (ZMod p) p N z

noncomputable def relSet : Set (TruncatedWittVector p N (C p B N)) :=
  {ρ | (∃ z w : M p B, ρ = u p B N (z + w) - u p B N z - u p B N w) ∨
    (∃ z : M p B, ρ = TruncWitt.frobeniusFun (u p B N z) -
      u p B N (DieudonneModule.frobenius (ZMod p) p B z)) ∨
    (∃ z : M p B, ρ = TruncWitt.verschiebung (u p B N z) -
      u p B N (DieudonneModule.verschiebung (ZMod p) p B z))}

noncomputable def relCoords : Set (C p B N) := {c | ∃ ρ ∈ relSet p B N, ∃ i : Fin N, ρ.coeff i = c}

noncomputable def relIdeal : Ideal (C p B N) := Ideal.span (relCoords p B N)

variable {p B N}

theorem u_mem_wittHom (z : M p B) : u p B N z ∈ wittHom (ZMod p) p N (C p B N) :=
  WittGroup.univ_mem_wittHom z

theorem mem_wittHom_of_mem_relSet {ρ : TruncatedWittVector p N (C p B N)} (hρ : ρ ∈ relSet p B N) :
    ρ ∈ wittHom (ZMod p) p N (C p B N) := by
  rcases hρ with ⟨z, w, rfl⟩ | ⟨z, rfl⟩ | ⟨z, rfl⟩
  · exact sub_mem (sub_mem (u_mem_wittHom _) (u_mem_wittHom _)) (u_mem_wittHom _)
  · exact sub_mem (frobeniusFun_mem_wittHom (R := ZMod p) (u_mem_wittHom _)) (u_mem_wittHom _)
  · exact sub_mem (verschiebung_mem_wittHom (R := ZMod p) (u_mem_wittHom _)) (u_mem_wittHom _)

theorem coeff_mem_relIdeal {ρ : TruncatedWittVector p N (C p B N)} (hρ : ρ ∈ relSet p B N)
    (i : Fin N) : ρ.coeff i ∈ relIdeal p B N :=
  Ideal.subset_span ⟨ρ, hρ, i, rfl⟩

theorem map_eq_zero_of_relIdeal_le_ker {T : Type w} [CommRing T] (g : C p B N →+* T)
    (hg : relIdeal p B N ≤ RingHom.ker g) {ρ : TruncatedWittVector p N (C p B N)}
    (hρ : ρ ∈ relSet p B N) : TruncWitt.map (p := p) g ρ = 0 :=
  TruncatedWittVector.ext fun i => by
    rw [TruncWitt.coeff_map, TruncatedWittVector.coeff_zero]
    exact hg (coeff_mem_relIdeal hρ i)

theorem relIdeal_le_ker_of_forall_map_eq_zero {T : Type w} [CommRing T] (g : C p B N →+* T)
    (hg : ∀ ρ ∈ relSet p B N, TruncWitt.map (p := p) g ρ = 0) : relIdeal p B N ≤ RingHom.ker g := by
  rw [relIdeal, Ideal.span_le]
  rintro c ⟨ρ, hρ, i, rfl⟩
  rw [SetLike.mem_coe, RingHom.mem_ker, ← TruncWitt.coeff_map (p := p) g, hg ρ hρ,
    TruncatedWittVector.coeff_zero]

theorem map_mk_eq_zero {ρ : TruncatedWittVector p N (C p B N)} (hρ : ρ ∈ relSet p B N) :
    TruncWitt.map (p := p) (Ideal.Quotient.mk (relIdeal p B N)) ρ = 0 :=
  map_eq_zero_of_relIdeal_le_ker _ (le_of_eq Ideal.mk_ker.symm) hρ

theorem map_antipode_of_mem_wittHom {R : Type w} [CommRing R] {H : Type v} [CommRing H]
    [HopfAlgebra R H] {n : ℕ} {x : TruncatedWittVector p n H} (hx : x ∈ wittHom R p n H) :
    TruncWitt.map (HopfAlgebra.antipodeAlgHom R H).toRingHom x = -x := by
  have h := map_convMul_of_mem_wittHom (T := H) hx (WithConv.toConv (AlgHom.id R H))
    (WithConv.toConv ((AlgHom.id R H).comp (HopfAlgebra.antipodeAlgHom R H)))
  rw [HopfAlgebra.convMul_comp_antipodeAlgHom (AlgHom.id R H)] at h
  have h1 : TruncWitt.map (1 : WithConv (H →ₐ[R] H)).ofConv.toRingHom x = 0 := by
    have hfac : (1 : WithConv (H →ₐ[R] H)).ofConv.toRingHom =
        (algebraMap R H).comp (Bialgebra.counitAlgHom R H).toRingHom := by
      refine RingHom.ext fun c => ?_
      simp [AlgHom.convOne_apply]
    rw [hfac, ← TruncWitt.map_map, map_counit_of_mem_wittHom hx, map_zero]
  rw [h1, WithConv.ofConv_toConv, WithConv.ofConv_toConv] at h
  have hid : TruncWitt.map (AlgHom.id R H).toRingHom x = x := TruncWitt.map_id x
  rw [hid] at h
  have h' : TruncWitt.map ((AlgHom.id R H).comp (HopfAlgebra.antipodeAlgHom R H)).toRingHom x = -x :=
    eq_neg_of_add_eq_zero_right h.symm
  simpa using h'

theorem apply_eq_zero_of_mem_relIdeal {T : Type w} [CommRing T] (g : C p B N →+* T)
    (hg : ∀ ρ ∈ relSet p B N, TruncWitt.map (p := p) g ρ = 0) {x : C p B N}
    (hx : x ∈ relIdeal p B N) : g x = 0 :=
  RingHom.mem_ker.1 (relIdeal_le_ker_of_forall_map_eq_zero g hg hx)

noncomputable abbrev comulQuot : C p B N →+* (C p B N ⧸ relIdeal p B N) ⊗[ZMod p] (C p B N ⧸ relIdeal p B N) :=
  (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ (ZMod p) (relIdeal p B N))
      (Ideal.Quotient.mkₐ (ZMod p) (relIdeal p B N))).toRingHom.comp (comulRingHom (ZMod p) (C p B N))

theorem map_comulQuot_eq_zero {ρ : TruncatedWittVector p N (C p B N)} (hρ : ρ ∈ relSet p B N) :
    TruncWitt.map (p := p) (comulQuot (p := p) (B := B) (N := N)) ρ = 0 := by
  have hρ' := (mem_wittHom_iff ρ).1 (mem_wittHom_of_mem_relSet hρ)
  have hmk : TruncWitt.map (p := p) (Ideal.Quotient.mkₐ (ZMod p) (relIdeal p B N)).toRingHom ρ = 0 :=
    map_mk_eq_zero hρ
  have h₁ : (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ (ZMod p) (relIdeal p B N))
        (Ideal.Quotient.mkₐ (ZMod p) (relIdeal p B N))).toRingHom.comp
        (Algebra.TensorProduct.includeLeft : C p B N →ₐ[ZMod p] C p B N ⊗[ZMod p] C p B N).toRingHom =
      (Algebra.TensorProduct.includeLeft :
          (C p B N ⧸ relIdeal p B N) →ₐ[ZMod p] _ ⊗[ZMod p] (C p B N ⧸ relIdeal p B N)).toRingHom.comp
        (Ideal.Quotient.mkₐ (ZMod p) (relIdeal p B N)).toRingHom := by
    refine RingHom.ext fun c => ?_
    simp
  have h₂ : (Algebra.TensorProduct.map (Ideal.Quotient.mkₐ (ZMod p) (relIdeal p B N))
        (Ideal.Quotient.mkₐ (ZMod p) (relIdeal p B N))).toRingHom.comp
        (Algebra.TensorProduct.includeRight : C p B N →ₐ[ZMod p] C p B N ⊗[ZMod p] C p B N).toRingHom =
      (Algebra.TensorProduct.includeRight :
          (C p B N ⧸ relIdeal p B N) →ₐ[ZMod p] (C p B N ⧸ relIdeal p B N) ⊗[ZMod p] _).toRingHom.comp
        (Ideal.Quotient.mkₐ (ZMod p) (relIdeal p B N)).toRingHom := by
    refine RingHom.ext fun c => ?_
    simp
  rw [← TruncWitt.map_map, hρ', map_add, TruncWitt.map_map, TruncWitt.map_map, h₁, h₂,
    ← TruncWitt.map_map, ← TruncWitt.map_map, hmk, map_zero, map_zero, add_zero]

theorem relIdeal_le_of_forall_coeff_mem {J : Ideal (C p B N)}
    (h : ∀ ρ ∈ relSet p B N, ∀ i : Fin N, ρ.coeff i ∈ J) : relIdeal p B N ≤ J :=
  Ideal.span_le.2 (by rintro c ⟨ρ, hρ, i, rfl⟩; exact h ρ hρ i)

theorem relIdeal_le_comap_antipode :
    relIdeal p B N ≤ (relIdeal p B N).comap (HopfAlgebra.antipodeAlgHom (ZMod p) (C p B N)).toRingHom := by
  refine relIdeal_le_of_forall_coeff_mem fun ρ hρ i => ?_
  have key : Ideal.Quotient.mk (relIdeal p B N)
      ((HopfAlgebra.antipodeAlgHom (ZMod p) (C p B N)).toRingHom (ρ.coeff i)) = 0 := by
    rw [← TruncWitt.coeff_map (p := p) (HopfAlgebra.antipodeAlgHom (ZMod p) (C p B N)).toRingHom ρ i,
      map_antipode_of_mem_wittHom (R := ZMod p) (H := C p B N) (mem_wittHom_of_mem_relSet hρ),
      ← TruncWitt.coeff_map (p := p) (Ideal.Quotient.mk (relIdeal p B N)) (-ρ) i, map_neg,
      map_mk_eq_zero hρ, neg_zero, TruncatedWittVector.coeff_zero]
  exact Ideal.mem_comap.2 (Ideal.Quotient.eq_zero_iff_mem.1 key)

scoped instance relIdeal_isHopfIdeal : (relIdeal p B N).IsHopfIdeal' (ZMod p) where
  map_mkₐ_comul_eq_zero x hx :=
    apply_eq_zero_of_mem_relIdeal (comulQuot (p := p) (B := B) (N := N))
      (fun _ hρ => map_comulQuot_eq_zero hρ) hx
  counit_eq_zero x hx :=
    apply_eq_zero_of_mem_relIdeal (Bialgebra.counitAlgHom (ZMod p) (C p B N)).toRingHom
      (fun _ hρ => map_counit_of_mem_wittHom (mem_wittHom_of_mem_relSet hρ)) hx
  antipode_mem x hx := by
    have h := Ideal.mem_comap.1 (relIdeal_le_comap_antipode hx)
    exact h

variable (p B N)

abbrev A : Type u := C p B N ⧸ relIdeal p B N

noncomputable abbrev π : C p B N →ₐc[ZMod p] A p B N := HopfAlgebra.quotientBialgHom (ZMod p) (relIdeal p B N)

theorem π_toRingHom : ((π p B N : C p B N →ₐ[ZMod p] A p B N)).toRingHom =
    Ideal.Quotient.mk (relIdeal p B N) := rfl

noncomputable def ubar (z : M p B) : wittHom (ZMod p) p N (A p B N) :=
  wittHomMap p N (π p B N) ⟨u p B N z, u_mem_wittHom z⟩

theorem coe_ubar (z : M p B) : (ubar p B N z : TruncatedWittVector p N (A p B N)) =
    TruncWitt.map (Ideal.Quotient.mk (relIdeal p B N)) (u p B N z) := rfl

variable {p B N}

theorem ubar_add (z w : M p B) : ubar p B N (z + w) = ubar p B N z + ubar p B N w := by
  apply Subtype.ext
  have h := map_mk_eq_zero (p := p) (B := B) (N := N) (Or.inl ⟨z, w, rfl⟩)
  rw [map_sub, map_sub, sub_eq_zero, sub_eq_iff_eq_add] at h
  rw [AddSubgroup.coe_add, coe_ubar, coe_ubar, coe_ubar, h, add_comm]

theorem ubar_zero : ubar p B N 0 = 0 := by
  have h := ubar_add (p := p) (B := B) (N := N) 0 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem ubar_frobenius (z : M p B) :
    ubar p B N (DieudonneModule.frobenius (ZMod p) p B z) = wittHomFrobenius (ZMod p) p N (A p B N) (ubar p B N z) := by
  apply Subtype.ext
  have h := map_mk_eq_zero (p := p) (B := B) (N := N) (Or.inr (Or.inl ⟨z, rfl⟩))
  rw [map_sub, sub_eq_zero, TruncWitt.map_frobeniusFun] at h
  rw [coe_wittHomFrobenius, coe_ubar, coe_ubar, h]

theorem ubar_verschiebung (z : M p B) :
    ubar p B N (DieudonneModule.verschiebung (ZMod p) p B z) =
      wittHomVerschiebung (ZMod p) p N (A p B N) (ubar p B N z) := by
  apply Subtype.ext
  have h := map_mk_eq_zero (p := p) (B := B) (N := N) (Or.inr (Or.inr ⟨z, rfl⟩))
  rw [map_sub, sub_eq_zero, TruncWitt.map_verschiebung] at h
  rw [coe_wittHomVerschiebung, coe_ubar, coe_ubar, h]

variable (p B N)

noncomputable def ψ : M p B →+ DieudonneModule (ZMod p) p (A p B N) where
  toFun z := of (ZMod p) p (A p B N) N (ubar p B N z)
  map_zero' := by rw [ubar_zero, map_zero]
  map_add' z w := by rw [ubar_add, map_add]

theorem ψ_apply (z : M p B) : ψ p B N z = of (ZMod p) p (A p B N) N (ubar p B N z) := rfl

theorem ψ_frobenius (z : M p B) :
    ψ p B N (DieudonneModule.frobenius (ZMod p) p B z) =
      DieudonneModule.frobenius (ZMod p) p (A p B N) (ψ p B N z) := by
  rw [ψ_apply, ψ_apply, frobenius_of, ubar_frobenius]

theorem ψ_verschiebung (z : M p B) :
    ψ p B N (DieudonneModule.verschiebung (ZMod p) p B z) =
      DieudonneModule.verschiebung (ZMod p) p (A p B N) (ψ p B N z) := by
  rw [ψ_apply, ψ_apply, verschiebung_of, ubar_verschiebung]

noncomputable abbrev Nψ : AddSubgroup (DieudonneModule (ZMod p) p (A p B N)) := (ψ p B N).range

scoped instance finite_Nψ [Finite (M p B)] : Finite (Nψ p B N) := by
  have : (Nψ p B N : Set (DieudonneModule (ZMod p) p (A p B N))) = Set.range (ψ p B N) :=
    AddMonoidHom.coe_range _
  have hfin : (Set.range (ψ p B N)).Finite := Set.finite_range _
  rw [← this] at hfin
  exact hfin.to_subtype

theorem frobenius_mem_Nψ {y : DieudonneModule (ZMod p) p (A p B N)} (hy : y ∈ Nψ p B N) :
    DieudonneModule.frobenius (ZMod p) p (A p B N) y ∈ Nψ p B N := by
  obtain ⟨z, rfl⟩ := hy
  exact ⟨DieudonneModule.frobenius (ZMod p) p B z, ψ_frobenius p B N z⟩

theorem verschiebung_mem_Nψ {y : DieudonneModule (ZMod p) p (A p B N)} (hy : y ∈ Nψ p B N) :
    DieudonneModule.verschiebung (ZMod p) p (A p B N) y ∈ Nψ p B N := by
  obtain ⟨z, rfl⟩ := hy
  exact ⟨DieudonneModule.verschiebung (ZMod p) p B z, ψ_verschiebung p B N z⟩

theorem adjoin_coords_eq_top :
    Algebra.adjoin (ZMod p) {c : A p B N | ∃ (n : ℕ) (x : wittHom (ZMod p) p n (A p B N)) (i : Fin n),
        of (ZMod p) p (A p B N) n x ∈ Nψ p B N ∧ (x : TruncatedWittVector p n (A p B N)).coeff i = c} = ⊤ := by
  rw [eq_top_iff]

  rintro a -
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective a
  change (Ideal.Quotient.mkₐ (ZMod p) (relIdeal p B N)) c ∈ _
  have hc : c ∈ (⊤ : Subalgebra (ZMod p) (C p B N)) := Algebra.mem_top
  have hgen : (⊤ : Subalgebra (ZMod p) (C p B N)) =
      Algebra.adjoin (ZMod p) (Set.range fun ji : M p B × Fin N => (WittGroup.X ji.1 ji.2 : C p B N)) := by
    change (⊤ : Subalgebra (ZMod p) (MvPolynomial (M p B × Fin N) (ZMod p))) = _
    exact (MvPolynomial.adjoin_range_X).symm
  rw [hgen] at hc
  rw [← Subalgebra.mem_comap]
  refine (Algebra.adjoin_le ?_) hc
  rintro _ ⟨⟨z, i⟩, rfl⟩
  rw [SetLike.mem_coe, Subalgebra.mem_comap]
  refine Algebra.subset_adjoin ⟨N, ubar p B N z, i, ⟨z, rfl⟩, ?_⟩
  rw [coe_ubar, TruncWitt.coeff_map, WittGroup.coeff_univ]
  rfl

theorem moduleFinite_A [Finite (M p B)] : Module.Finite (ZMod p) (A p B N) := by
  obtain ⟨hfin, -⟩ := Deformation.DieudonneModule.finrank_adjoin_coeff_le_natCard (ZMod p) p (A p B N)
    (Nψ p B N) (fun y hy => frobenius_mem_Nψ p B N hy) (fun y hy => verschiebung_mem_Nψ p B N hy)
  rw [adjoin_coords_eq_top] at hfin
  exact Module.Finite.of_surjective (Subalgebra.topEquiv (R := ZMod p) (A := A p B N)).toLinearMap
    (Subalgebra.topEquiv (R := ZMod p) (A := A p B N)).surjective

end Envelope

section Point

variable {p : ℕ} [hp : Fact p.Prime]
variable {B : Type u} [CommRing B] [HopfAlgebra (ZMod p) B]
variable {N : ℕ} (hN : ∀ z : M p B, ∃ x : wittHom (ZMod p) p N B, of (ZMod p) p B N x = z)
variable {S : Type v} [CommRing S] [Algebra (ZMod p) S]
variable (φ : M p B →+ UnipotentWittCovector p S)
  (hφF : ∀ z, φ (DieudonneModule.frobenius (ZMod p) p B z) = UnipotentWittCovector.frobenius (ZMod p) p S (φ z))
  (hφV : ∀ z, φ (DieudonneModule.verschiebung (ZMod p) p B z) = UnipotentWittCovector.verschiebung p S (φ z))

omit [Algebra (ZMod p) S] in
include hN hφV in

theorem exists_of_eq (z : M p B) : ∃ s : TruncatedWittVector p N S, UnipotentWittCovector.of p S N s = φ z := by
  apply UnipotentWittCovector.exists_of_eq_of_verschiebung_iterate_eq_zero
  obtain ⟨x, rfl⟩ := hN z
  have hsemi : Semiconj φ (DieudonneModule.verschiebung (ZMod p) p B)
      (UnipotentWittCovector.verschiebung p S) := hφV
  rw [← (hsemi.iterate_right N).eq, verschiebung_iterate_of_self, map_zero]

noncomputable def sv (z : M p B) : TruncatedWittVector p N S := Classical.choose (exists_of_eq hN φ hφV z)

omit [Algebra (ZMod p) S] in
theorem of_sv (z : M p B) : UnipotentWittCovector.of p S N (sv hN φ hφV z) = φ z :=
  Classical.choose_spec (exists_of_eq hN φ hφV z)

noncomputable def σC : C p B N →ₐ[ZMod p] S := WittGroup.lift fun z i => (sv hN φ hφV z).coeff i

theorem map_σC_u (z : M p B) : TruncWitt.map (σC hN φ hφV).toRingHom (u p B N z) = sv hN φ hφV z := by
  rw [WittGroup.map_univ]
  refine TruncatedWittVector.ext fun i => ?_
  rw [TruncatedWittVector.coeff_mk]
  exact WittGroup.lift_X _ z i

include hφF in

theorem relIdeal_le_ker_σC : relIdeal p B N ≤ RingHom.ker (σC hN φ hφV).toRingHom := by
  refine relIdeal_le_ker_of_forall_map_eq_zero _ fun ρ hρ => ?_
  have hinj := UnipotentWittCovector.of_injective (p := p) (S := S) N
  rcases hρ with ⟨z, w, rfl⟩ | ⟨z, rfl⟩ | ⟨z, rfl⟩
  · rw [map_sub, map_sub, map_σC_u, map_σC_u, map_σC_u]
    apply hinj
    rw [map_sub, map_sub, of_sv, of_sv, of_sv, map_add, map_zero]
    abel
  · rw [map_sub, TruncWitt.map_frobeniusFun, map_σC_u, map_σC_u]
    apply hinj
    rw [map_sub, of_sv, ← UnipotentWittCovector.frobenius_of (ZMod p), of_sv, hφF, sub_self, map_zero]
  · rw [map_sub, TruncWitt.map_verschiebung, map_σC_u, map_σC_u]
    apply hinj
    rw [map_sub, of_sv, ← UnipotentWittCovector.verschiebung_of, of_sv, hφV, sub_self, map_zero]

noncomputable def σA : A p B N →ₐ[ZMod p] S :=
  HopfAlgebra.quotientLiftPoint (ZMod p) (relIdeal p B N) (σC hN φ hφV)
    (fun _ hx => relIdeal_le_ker_σC hN φ hφF hφV hx)

theorem σA_comp_mk : (σA hN φ hφF hφV).toRingHom.comp (Ideal.Quotient.mk (relIdeal p B N)) =
    (σC hN φ hφV).toRingHom :=
  RingHom.ext fun _ => rfl

theorem map_σA_ubar (z : M p B) :
    TruncWitt.map (σA hN φ hφF hφV).toRingHom (ubar p B N z : TruncatedWittVector p N (A p B N)) =
      sv hN φ hφV z := by
  rw [coe_ubar, TruncWitt.map_map, σA_comp_mk, map_σC_u]

end Point

section Surjective

variable (p : ℕ) [hp : Fact p.Prime]
variable (B : Type u) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
  [Module.Finite (ZMod p) B]

theorem finite_M (hB : IsLocalRing (CartierDual (ZMod p) B)) : Finite (M p B) := by
  haveI : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨L, -, hcard⟩ :=
    Deformation.DieudonneModule.exists_finrank_eq_pow_and_natCard_eq_pow_of_isLocalRing_cartierDual
      (ZMod p) p B hB
  refine Nat.finite_of_card_ne_zero ?_
  rw [hcard, Nat.card_zmod]
  exact pow_ne_zero _ hp.out.ne_zero

variable {S : Type v} [CommRing S] [Algebra (ZMod p) S]

theorem exists_eval_eq (hB : IsLocalRing (CartierDual (ZMod p) B))
    (φ : M p B →+ UnipotentWittCovector p S)
    (hφF : ∀ z, φ (DieudonneModule.frobenius (ZMod p) p B z) =
      UnipotentWittCovector.frobenius (ZMod p) p S (φ z))
    (hφV : ∀ z, φ (DieudonneModule.verschiebung (ZMod p) p B z) =
      UnipotentWittCovector.verschiebung p S (φ z)) :
    ∃ f : B →ₐ[ZMod p] S, DieudonneModule.eval (ZMod p) p f = φ := by
  haveI : Finite (M p B) := finite_M p B hB
  obtain ⟨N, hN⟩ := exists_level (R := ZMod p) (p := p) (C := B)
  haveI : Module.Finite (ZMod p) (A p B N) := moduleFinite_A p B N

  obtain ⟨g, hg⟩ := Deformation.DieudonneModule.exists_map_eq_of_isLocalRing_cartierDual p (A p B N) B hB
    (ψ p B N) (ψ_frobenius p B N) (ψ_verschiebung p B N)

  refine ⟨(σA hN φ hφF hφV).comp (g : B →ₐ[ZMod p] A p B N), AddMonoidHom.ext fun z => ?_⟩
  obtain ⟨x, rfl⟩ := hN z
  have hgx : (wittHomMap p N g x : TruncatedWittVector p N (A p B N)) = ubar p B N (of (ZMod p) p B N x) := by
    have h := DFunLike.congr_fun hg (of (ZMod p) p B N x)
    rw [map_of, ψ_apply] at h
    exact congrArg Subtype.val (of_injective N h)
  rw [eval_of, ← of_sv hN φ hφV (of (ZMod p) p B N x), ← map_σA_ubar hN φ hφF hφV, ← hgx,
    coe_wittHomMap, TruncWitt.map_map]
  rfl

end Surjective

end DieudonnePoints
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual.DieudonnePoints"

theorem solution
    (p : ℕ) [Fact p.Prime]
    (B : Type u) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B] (hB : IsLocalRing (CartierDual (ZMod p) B))
    (S : Type v) [CommRing S] [Algebra (ZMod p) S] :
    (∀ f g : B →ₐ[ZMod p] S,
        Deformation.DieudonneModule.eval (ZMod p) p f = Deformation.DieudonneModule.eval (ZMod p) p g →
        f = g) ∧
    (∀ φ : Deformation.DieudonneModule (ZMod p) p B →+ Deformation.UnipotentWittCovector p S,
        (∀ z, φ (Deformation.DieudonneModule.frobenius (ZMod p) p B z) =
          Deformation.UnipotentWittCovector.frobenius (ZMod p) p S (φ z)) →
        (∀ z, φ (Deformation.DieudonneModule.verschiebung (ZMod p) p B z) =
          Deformation.UnipotentWittCovector.verschiebung p S (φ z)) →
        ∃ f : B →ₐ[ZMod p] S, Deformation.DieudonneModule.eval (ZMod p) p f = φ) :=
  ⟨fun _ _ h => DieudonnePoints.eval_injective p hB h,
    fun φ hF hV => DieudonnePoints.exists_eval_eq p B hB φ hF hV⟩

end S_Deformation_DieudonneModule_eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_Deformation_DieudonneModule_eval_injective_and_exists_eval_eq_of_isLocalRing_cartierDual (solution)
