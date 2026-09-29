-- Prove2me | solution 1 for Deformation.DieudonneModule.exists_map_eq_of_isLocalRing_cartierDual
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/9ec87245-f7ed-50ad-98dd-96b6675c0bc6

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom
import Definitions.Def_Dieudonne_WittHomColimit
import Definitions.Def_HopfAlgebra_CartierDual
import Theorems.Thm_Deformation_DieudonneModule_exists_surjective_of
import Theorems.Thm_Deformation_DieudonneModule_exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual
import Theorems.Thm_Deformation_DieudonneModule_finrank_adjoin_coeff_le_natCard
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Deformation_DieudonneModule_exists_map_eq_of_isLocalRing_cartierDual
p2m_attr_erase "instance" "HopfAlgebra.HopfKerHopf.instHopfAlgebra HopfAlgebra.HopfKerHopf.instCoalgebra HopfAlgebra.HopfKerHopf.instIsCocomm HopfAlgebra.HopfKerHopf.instBialgebra CartierDual.instIsCocommViaBialgebra CartierDual.instModuleFreeViaBialgebra CartierDual.instModuleFiniteViaBialgebra HopfAlgebra.IsHopfTower.refl"
p2m_attr_erase "simp" "ModpDieudonneRealization.mk.sizeOf_spec ModpDieudonneRealization.mk.injEq CartierDual.map_apply CartierDual.congr_apply CartierDual.congr_symm_apply CartierDual.pairing_apply CartierDual.mapAlgHom_apply CartierDual.mapLinear_apply HopfAlgebra.canAlgHom_tmul HopfAlgebra.canMap_tmul HopfAlgebra.HopfKerHopf.ι₂_comulK HopfAlgebra.HopfKerHopf.ι₃_tmul HopfAlgebra.HopfKerHopf.counitK_apply HopfAlgebra.HopfKerHopf.coe_antipodeK HopfAlgebra.HopfKerHopf.ι₂_tmul HopfAlgebra.HopfKerHopf.coe_antipode HopfAlgebra.HopfKerHopf.hopfKerVal_apply HopfAlgebra.HopfKerHopf.valL_apply HopfAlgebra.HopfKerHopf.ι₂_comul HopfAlgebra.HopfTower.quotientMap_mk HopfAlgebra.IsHopfSubalgebra.ι₂_comulK HopfAlgebra.IsHopfTower.toBialgHom_apply HopfAlgebra.IsHopfTower.reprMap_right HopfAlgebra.IsHopfSubalgebra.counitK_apply HopfAlgebra.IsHopfSubalgebra.coe_antipodeK HopfAlgebra.HopfTower.galoisInv_tmul HopfAlgebra.HopfTower.galoisFwd_tmul HopfAlgebra.mem_augIdeal HopfAlgebra.IsHopfTower.reprMap_index HopfAlgebra.HopfTower.antipodeAlgHom_apply HopfAlgebra.IsHopfTower.reprMap_left HopfAlgebra.IsHopfSubalgebra.ι₂_tmul HopfAlgebra.HopfTower.θ₁_tmul HopfAlgebra.HopfTower.fwdB_apply HopfAlgebra.HopfTower.invQuot_mk HopfAlgebra.HopfTower.translateEquiv_apply HopfAlgebra.HopfTower.θ₂_tmul HopfAlgebra.IsHopfSubalgebra.ι₃_tmul"

set_option autoImplicit false

open scoped TensorProduct

universe u v w

namespace DieudonneFull

open Deformation Deformation.DieudonneModule Function

section KerV

variable {R : Type u} [CommRing R] {p : ℕ} [hp : Fact p.Prime]
variable {C : Type v} [CommRing C] [Bialgebra R C]

theorem coe_verschiebung_iterate {L : ℕ} (y : wittHom R p L C) (n : ℕ) :
    (((wittHomVerschiebung R p L C)^[n] y : wittHom R p L C) : TruncatedWittVector p L C) =
      (TruncWitt.verschiebung (p := p) (R := C))^[n] y := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iterate_succ_apply', iterate_succ_apply', ← ih]; rfl

theorem truncWitt_verschiebung_iterate_truncate {L : ℕ} (Y : WittVector p C) (n : ℕ) :
    (TruncWitt.verschiebung (p := p) (n := L) (R := C))^[n] (WittVector.truncate L Y) =
      WittVector.truncate L ((WittVector.verschiebung (p := p) (R := C))^[n] Y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', ih, TruncWitt.verschiebung_truncate,
      ← iterate_succ_apply' (f := WittVector.verschiebung)]

theorem verschiebung_iterate_of {L : ℕ} (y : wittHom R p L C) (n : ℕ) :
    (verschiebung R p C)^[n] (of R p C L y) = of R p C L ((wittHomVerschiebung R p L C)^[n] y) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply', ih, verschiebung_of]
    exact congrArg (of R p C L) (iterate_succ_apply' (wittHomVerschiebung R p L C) n y).symm

theorem exists_of_eq_of_verschiebung_iterate_eq_zero {n : ℕ} {z : DieudonneModule R p C}
    (hz : (verschiebung R p C)^[n] z = 0) : ∃ x : wittHom R p n C, of R p C n x = z := by
  obtain ⟨m, y₀, rfl⟩ := exists_of z
  set L := m + n with hL
  have hnL : n ≤ L := Nat.le_add_left n m
  set y : wittHom R p L C := wittHomShiftLE R p C (Nat.le_add_right m n) y₀ with hy
  have hyz : of R p C L y = of R p C m y₀ := of_shiftLE _ _
  rw [← hyz] at hz ⊢
  rw [verschiebung_iterate_of] at hz
  have hVy : (wittHomVerschiebung R p L C)^[n] y = 0 :=
    of_injective L (hz.trans (map_zero _).symm)
  have hcoe := congrArg (fun t : wittHom R p L C => (t : TruncatedWittVector p L C)) hVy
  simp only [coe_verschiebung_iterate, ZeroMemClass.coe_zero] at hcoe
  obtain ⟨Y, hY⟩ := WittVector.truncate_surjective p L C (y : TruncatedWittVector p L C)
  have hlow : ∀ i : Fin L, (i : ℕ) < L - n → (y : TruncatedWittVector p L C).coeff i = 0 := by
    intro i hi
    have h1 : ((TruncWitt.verschiebung (p := p) (n := L) (R := C))^[n] y).coeff
        ⟨i + n, by omega⟩ = 0 := by
      rw [hcoe]; exact TruncatedWittVector.coeff_zero (p := p) _ _ _
    rw [← hY, truncWitt_verschiebung_iterate_truncate, WittVector.coeff_truncate] at h1
    change ((WittVector.verschiebung (p := p) (R := C))^[n] Y).coeff (i + n) = 0 at h1
    rw [WittVector.iterate_verschiebung_coeff] at h1
    rw [← hY, WittVector.coeff_truncate]
    exact h1
  let x : TruncatedWittVector p n C :=
    TruncatedWittVector.mk p fun j : Fin n => (y : TruncatedWittVector p L C).coeff ⟨j + (L - n), by omega⟩
  have hx : TruncWitt.shiftLE hnL x = (y : TruncatedWittVector p L C) := by
    refine TruncatedWittVector.ext fun i => ?_
    rw [TruncWitt.coeff_shiftLE]
    split_ifs with hi
    · simp only [x, TruncatedWittVector.coeff_mk]
      congr 1
      exact Fin.ext (by simp only; omega)
    · exact (hlow i (by omega)).symm
  have hxmem : x ∈ wittHom R p n C := by
    rw [← shiftLE_mem_wittHom_iff hnL, hx]; exact y.2
  refine ⟨⟨x, hxmem⟩, ?_⟩
  rw [← of_shiftLE hnL]
  congr 1
  exact Subtype.ext hx

end KerV

section Incl

variable (k : Type u) [CommRing k]
variable (A : Type v) [CommRing A] [Bialgebra k A]
variable (B : Type w) [CommRing B] [Bialgebra k B]

noncomputable def inlB : A →ₐc[k] A ⊗[k] B :=
  (BialgHom.lTensor A (Bialgebra.unitBialgHom k B)).comp
    ((Bialgebra.TensorProduct.rid k k A).symm : A →ₐc[k] A ⊗[k] k)

noncomputable def inrB : B →ₐc[k] A ⊗[k] B :=
  (BialgHom.rTensor B (Bialgebra.unitBialgHom k A)).comp
    ((Bialgebra.TensorProduct.lid k B).symm : B →ₐc[k] k ⊗[k] B)

@[scoped simp] theorem inlB_apply (a : A) : inlB k A B a = a ⊗ₜ[k] 1 := by
  simp [inlB, Bialgebra.unitBialgHom]

@[scoped simp] theorem inrB_apply (b : B) : inrB k A B b = 1 ⊗ₜ[k] b := by
  simp [inrB, Bialgebra.unitBialgHom]

theorem inlB_toRingHom :
    ((inlB k A B : A →ₐc[k] A ⊗[k] B) : A →ₐ[k] A ⊗[k] B).toRingHom =
      (Algebra.TensorProduct.includeLeft : A →ₐ[k] A ⊗[k] B).toRingHom :=
  RingHom.ext fun a => by simp

theorem inrB_toRingHom :
    ((inrB k A B : B →ₐc[k] A ⊗[k] B) : B →ₐ[k] A ⊗[k] B).toRingHom =
      (Algebra.TensorProduct.includeRight : B →ₐ[k] A ⊗[k] B).toRingHom :=
  RingHom.ext fun a => by simp

end Incl

section WittSub

variable {p : ℕ} [hp : Fact p.Prime] {n : ℕ}
variable {k : Type u} [CommRing k] {T : Type v} [CommRing T] [Algebra k T]

omit hp in
theorem coeff_out_mem (S : Subalgebra k T) (x : TruncatedWittVector p n T)
    (hx : ∀ j, x.coeff j ∈ S) (i : ℕ) : x.out.coeff i ∈ S := by
  by_cases hi : i < n
  · have := TruncatedWittVector.coeff_out x ⟨i, hi⟩
    rw [Fin.val_mk] at this
    rw [this]
    exact hx _
  · have : x.out.coeff i = 0 := by
      change (if h : i < n then x.coeff ⟨i, h⟩ else 0) = 0
      rw [dif_neg hi]
    rw [this]
    exact zero_mem _

theorem coeff_sub_mem (S : Subalgebra k T) (u v : TruncatedWittVector p n T)
    (hu : ∀ j, u.coeff j ∈ S) (hv : ∀ j, v.coeff j ∈ S) (i : Fin n) : (u - v).coeff i ∈ S := by
  have hu' : WittVector.truncate n u.out = u := TruncatedWittVector.truncateFun_out u
  have hv' : WittVector.truncate n v.out = v := TruncatedWittVector.truncateFun_out v
  rw [← hu', ← hv', ← map_sub, WittVector.coeff_truncate, WittVector.sub_coeff]
  unfold WittVector.peval
  rw [MvPolynomial.aeval_def]
  refine MvPolynomial.eval₂_mem (fun m _ => ?_) (fun ij => ?_)
  · rw [eq_intCast]
    exact intCast_mem S _
  · obtain ⟨a, j⟩ := ij
    change (![u.out.coeff, v.out.coeff] a) j ∈ S
    fin_cases a
    · exact coeff_out_mem S u hu j
    · exact coeff_out_mem S v hv j

end WittSub

section Level

variable {R : Type u} [CommRing R] {p : ℕ} [hp : Fact p.Prime]
variable {C : Type v} [CommRing C] [Bialgebra R C]

theorem coeff_eq_zero_or_eq_coeff_of_of_eq {n m : ℕ} (x : wittHom R p n C) (x' : wittHom R p m C)
    (h : of R p C n x = of R p C m x') (i : Fin n) :
    (x : TruncatedWittVector p n C).coeff i = 0 ∨
      ∃ j : Fin m, (x : TruncatedWittVector p n C).coeff i = (x' : TruncatedWittVector p m C).coeff j := by
  rw [of_eq_of_iff] at h
  have hc := congrArg (fun t : wittHom R p (max n m) C =>
    (t : TruncatedWittVector p (max n m) C).coeff ⟨i + (max n m - n), by omega⟩) h
  simp only [coe_wittHomShiftLE] at hc
  rw [TruncWitt.coeff_shiftLE_add] at hc
  rw [TruncWitt.coeff_shiftLE] at hc
  split_ifs at hc with hle
  · exact Or.inr ⟨_, hc⟩
  · exact Or.inl hc

end Level

section Main

set_option linter.unusedSectionVars false

variable (p : ℕ) [hp : Fact p.Prime]
variable (A : Type u) [CommRing A] [Bialgebra (ZMod p) A] [Module.Finite (ZMod p) A]
variable (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
  [Module.Finite (ZMod p) B]

local notation "𝕜" => ZMod p

theorem natCard_le_finrank (hB : IsLocalRing (CartierDual 𝕜 B)) :
    Nat.card (DieudonneModule 𝕜 p B) ≤ Module.finrank 𝕜 B := by
  obtain ⟨L, h1, h2⟩ :=
    Deformation.DieudonneModule.exists_finrank_eq_pow_and_natCard_le_pow_of_isLocalRing_cartierDual
      𝕜 p B hB
  rw [h1]; simpa [Nat.card_zmod] using h2

variable {p A B}

structure Setup where
  N : ℕ
  hN : Surjective (of 𝕜 p B N)
  φ : DieudonneModule 𝕜 p B →+ DieudonneModule 𝕜 p A
  hF : ∀ z, φ (frobenius 𝕜 p B z) = frobenius 𝕜 p A (φ z)
  hV : ∀ z, φ (verschiebung 𝕜 p B z) = verschiebung 𝕜 p A (φ z)

namespace Setup

variable (S : Setup (p := p) (A := A) (B := B))

theorem exists_level (x : wittHom 𝕜 p S.N B) :
    ∃ y : wittHom 𝕜 p S.N A, of 𝕜 p A S.N y = S.φ (of 𝕜 p B S.N x) := by
  refine exists_of_eq_of_verschiebung_iterate_eq_zero ?_
  have hsemi : Semiconj S.φ (verschiebung 𝕜 p B) (verschiebung 𝕜 p A) := S.hV
  rw [← hsemi.iterate_right S.N, verschiebung_iterate_of, wittHomVerschiebung_iterate_eq_zero,
    map_zero, map_zero]

noncomputable def Y : wittHom 𝕜 p S.N B →+ wittHom 𝕜 p S.N A where
  toFun x := Classical.choose (S.exists_level x)
  map_zero' := of_injective S.N (by
    rw [Classical.choose_spec (S.exists_level 0), map_zero, map_zero, map_zero])
  map_add' x x' := of_injective S.N (by
    rw [Classical.choose_spec (S.exists_level (x + x')), map_add, map_add, map_add,
      Classical.choose_spec (S.exists_level x), Classical.choose_spec (S.exists_level x')])

theorem of_Y (x : wittHom 𝕜 p S.N B) : of 𝕜 p A S.N (S.Y x) = S.φ (of 𝕜 p B S.N x) :=
  Classical.choose_spec (S.exists_level x)

theorem Y_frobenius (x : wittHom 𝕜 p S.N B) :
    S.Y (wittHomFrobenius 𝕜 p S.N B x) = wittHomFrobenius 𝕜 p S.N A (S.Y x) :=
  of_injective S.N (by rw [of_Y, ← frobenius_of, ← frobenius_of, S.hF, of_Y])

theorem Y_verschiebung (x : wittHom 𝕜 p S.N B) :
    S.Y (wittHomVerschiebung 𝕜 p S.N B x) = wittHomVerschiebung 𝕜 p S.N A (S.Y x) :=
  of_injective S.N (by rw [of_Y, ← verschiebung_of, ← verschiebung_of, S.hV, of_Y])

noncomputable def Z : wittHom 𝕜 p S.N B →+ wittHom 𝕜 p S.N (A ⊗[𝕜] B) :=
  (wittHomMap p S.N (inlB 𝕜 A B)).comp S.Y - wittHomMap p S.N (inrB 𝕜 A B)

theorem Z_apply (x : wittHom 𝕜 p S.N B) :
    S.Z x = wittHomMap p S.N (inlB 𝕜 A B) (S.Y x) - wittHomMap p S.N (inrB 𝕜 A B) x := rfl

theorem coe_Z (x : wittHom 𝕜 p S.N B) :
    (S.Z x : TruncatedWittVector p S.N (A ⊗[𝕜] B)) =
      TruncWitt.map (Algebra.TensorProduct.includeLeft : A →ₐ[𝕜] A ⊗[𝕜] B).toRingHom (S.Y x) -
      TruncWitt.map (Algebra.TensorProduct.includeRight : B →ₐ[𝕜] A ⊗[𝕜] B).toRingHom x := by
  rw [Z_apply, AddSubgroupClass.coe_sub, coe_wittHomMap, coe_wittHomMap, inlB_toRingHom,
    inrB_toRingHom]

noncomputable def Nφ : AddSubgroup (DieudonneModule 𝕜 p (A ⊗[𝕜] B)) :=
  ((of 𝕜 p (A ⊗[𝕜] B) S.N).comp S.Z).range

theorem mem_Nφ (x : wittHom 𝕜 p S.N B) : of 𝕜 p (A ⊗[𝕜] B) S.N (S.Z x) ∈ S.Nφ :=
  ⟨x, rfl⟩

theorem Nφ_frobenius (z : DieudonneModule 𝕜 p (A ⊗[𝕜] B)) (hz : z ∈ S.Nφ) :
    frobenius 𝕜 p (A ⊗[𝕜] B) z ∈ S.Nφ := by
  obtain ⟨x, rfl⟩ := hz
  refine ⟨wittHomFrobenius 𝕜 p S.N B x, ?_⟩
  simp only [AddMonoidHom.comp_apply, frobenius_of, Z_apply, map_sub, wittHomMap_frobenius,
    Y_frobenius]

theorem Nφ_verschiebung (z : DieudonneModule 𝕜 p (A ⊗[𝕜] B)) (hz : z ∈ S.Nφ) :
    verschiebung 𝕜 p (A ⊗[𝕜] B) z ∈ S.Nφ := by
  obtain ⟨x, rfl⟩ := hz
  refine ⟨wittHomVerschiebung 𝕜 p S.N B x, ?_⟩
  simp only [AddMonoidHom.comp_apply, verschiebung_of, Z_apply, map_sub, wittHomMap_verschiebung,
    Y_verschiebung]

theorem finite_wittHom (n : ℕ) : Finite (wittHom 𝕜 p n B) := by
  haveI : Finite B := Module.finite_of_finite 𝕜
  haveI : Finite (TruncatedWittVector p n B) := by
    unfold TruncatedWittVector; infer_instance
  infer_instance

scoped instance finite_Nφ : Finite S.Nφ := by
  haveI := finite_wittHom (p := p) (B := B) S.N
  change Finite (Set.range _)
  infer_instance

theorem natCard_Nφ_le (hB : IsLocalRing (CartierDual 𝕜 B)) :
    Nat.card S.Nφ ≤ Module.finrank 𝕜 B := by
  haveI := finite_wittHom (p := p) (B := B) S.N
  calc Nat.card S.Nφ ≤ Nat.card (wittHom 𝕜 p S.N B) :=
        Nat.card_le_card_of_surjective _ (AddMonoidHom.rangeRestrict_surjective _)
    _ = Nat.card (DieudonneModule 𝕜 p B) :=
        Nat.card_eq_of_bijective _ ⟨of_injective S.N, S.hN⟩
    _ ≤ Module.finrank 𝕜 B := natCard_le_finrank p B hB

noncomputable def D : Subalgebra 𝕜 (A ⊗[𝕜] B) :=
  Algebra.adjoin 𝕜 {c : A ⊗[𝕜] B | ∃ (n : ℕ) (x : wittHom 𝕜 p n (A ⊗[𝕜] B)) (i : Fin n),
    of 𝕜 p (A ⊗[𝕜] B) n x ∈ S.Nφ ∧ (x : TruncatedWittVector p n (A ⊗[𝕜] B)).coeff i = c}

theorem coeff_Z_mem_D (x : wittHom 𝕜 p S.N B) (i : Fin S.N) :
    (S.Z x : TruncatedWittVector p S.N (A ⊗[𝕜] B)).coeff i ∈ S.D :=
  Algebra.subset_adjoin ⟨S.N, S.Z x, i, S.mem_Nφ x, rfl⟩

theorem finite_D_and_finrank_D_le : Module.Finite 𝕜 S.D ∧ Module.finrank 𝕜 S.D ≤ Nat.card S.Nφ :=
  Deformation.DieudonneModule.finrank_adjoin_coeff_le_natCard 𝕜 p (A ⊗[𝕜] B) S.Nφ
    S.Nφ_frobenius S.Nφ_verschiebung

noncomputable def τ : A ⊗[𝕜] S.D →ₐ[𝕜] A ⊗[𝕜] B :=
  Algebra.TensorProduct.productMap (Algebra.TensorProduct.includeLeft : A →ₐ[𝕜] A ⊗[𝕜] B) S.D.val

theorem τ_tmul (a : A) (d : S.D) : S.τ (a ⊗ₜ[𝕜] d) = (a ⊗ₜ[𝕜] (1 : B)) * (d : A ⊗[𝕜] B) := by
  simp [τ, Algebra.TensorProduct.productMap_apply_tmul]

theorem one_tmul_coeff_mem_range (x : wittHom 𝕜 p S.N B) (i : Fin S.N) :
    (1 : A) ⊗ₜ[𝕜] (x : TruncatedWittVector p S.N B).coeff i ∈ S.τ.range := by

  have key : TruncWitt.map (Algebra.TensorProduct.includeRight : B →ₐ[𝕜] A ⊗[𝕜] B).toRingHom
      (x : TruncatedWittVector p S.N B) =
      TruncWitt.map (Algebra.TensorProduct.includeLeft : A →ₐ[𝕜] A ⊗[𝕜] B).toRingHom (S.Y x) -
        (S.Z x : TruncatedWittVector p S.N (A ⊗[𝕜] B)) := by
    rw [coe_Z]; abel
  have hcoeff := congrArg (TruncatedWittVector.coeff i) key
  rw [TruncWitt.coeff_map] at hcoeff
  change (1 : A) ⊗ₜ[𝕜] (x : TruncatedWittVector p S.N B).coeff i = _ at hcoeff
  rw [hcoeff]
  refine coeff_sub_mem S.τ.range _ _ (fun j => ?_) (fun j => ?_) i
  · rw [TruncWitt.coeff_map]
    refine ⟨((S.Y x : TruncatedWittVector p S.N A).coeff j) ⊗ₜ[𝕜] (1 : S.D), ?_⟩
    change S.τ _ = _
    rw [τ_tmul]; simp
  · refine ⟨(1 : A) ⊗ₜ[𝕜] ⟨_, S.coeff_Z_mem_D x j⟩, ?_⟩
    change S.τ _ = _
    rw [τ_tmul, ← Algebra.TensorProduct.one_def, one_mul]

theorem range_τ_eq_top (hB : IsLocalRing (CartierDual 𝕜 B)) : S.τ.range = ⊤ := by

  have hgen : ∀ b : B, (1 : A) ⊗ₜ[𝕜] b ∈ S.τ.range := by
    have hsub : Algebra.adjoin 𝕜 {b : B | ∃ (n : ℕ) (x : wittHom 𝕜 p n B) (i : Fin n),
        (x : TruncatedWittVector p n B).coeff i = b} ≤
        S.τ.range.comap (Algebra.TensorProduct.includeRight : B →ₐ[𝕜] A ⊗[𝕜] B) := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨n, x, i, rfl⟩
      obtain ⟨x', hx'⟩ := S.hN (of 𝕜 p B n x)
      rcases coeff_eq_zero_or_eq_coeff_of_of_eq x x' hx'.symm i with h0 | ⟨j, hj⟩
      · rw [SetLike.mem_coe, Subalgebra.mem_comap, h0, map_zero]; exact zero_mem _
      · rw [SetLike.mem_coe, Subalgebra.mem_comap, hj]
        exact S.one_tmul_coeff_mem_range x' j
    rw [Deformation.adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual 𝕜 p B hB, top_le_iff]
      at hsub
    intro b
    have : b ∈ (⊤ : Subalgebra 𝕜 B) := Algebra.mem_top
    rw [← hsub, Subalgebra.mem_comap] at this
    exact this
  rw [eq_top_iff, ← Algebra.TensorProduct.adjoin_tmul_eq_top, Algebra.adjoin_le_iff]
  rintro _ ⟨a, b, rfl⟩
  have : a ⊗ₜ[𝕜] b = (a ⊗ₜ[𝕜] (1 : B)) * ((1 : A) ⊗ₜ[𝕜] b) := by simp
  rw [this]
  exact mul_mem ⟨a ⊗ₜ[𝕜] 1, by change S.τ _ = _; rw [τ_tmul]; simp⟩ (hgen b)

theorem τ_bijective (hB : IsLocalRing (CartierDual 𝕜 B)) : Bijective S.τ := by
  haveI : Module.Finite 𝕜 S.D := S.finite_D_and_finrank_D_le.1
  have hsurj : Surjective S.τ := by
    rw [← AlgHom.range_eq_top]; exact S.range_τ_eq_top hB
  have hD : Module.finrank 𝕜 S.D ≤ Module.finrank 𝕜 B :=
    S.finite_D_and_finrank_D_le.2.trans (S.natCard_Nφ_le hB)
  have h1 : Module.finrank 𝕜 (A ⊗[𝕜] S.D) ≤ Module.finrank 𝕜 (A ⊗[𝕜] B) := by
    rw [Module.finrank_tensorProduct, Module.finrank_tensorProduct]
    exact Nat.mul_le_mul_left _ hD
  have h2 : Module.finrank 𝕜 (A ⊗[𝕜] B) ≤ Module.finrank 𝕜 (A ⊗[𝕜] S.D) := by
    have := LinearMap.finrank_range_le S.τ.toLinearMap
    rwa [LinearMap.range_eq_top.2 (by exact hsurj), finrank_top] at this
  have heq : Module.finrank 𝕜 (A ⊗[𝕜] S.D) = Module.finrank 𝕜 (A ⊗[𝕜] B) := le_antisymm h1 h2
  refine ⟨?_, hsurj⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank heq (f := S.τ.toLinearMap)).2
    hsurj

noncomputable def τEquiv (hB : IsLocalRing (CartierDual 𝕜 B)) : A ⊗[𝕜] S.D ≃ₐ[𝕜] A ⊗[𝕜] B :=
  AlgEquiv.ofBijective S.τ (S.τ_bijective hB)

theorem τEquiv_apply (hB : IsLocalRing (CartierDual 𝕜 B)) (z : A ⊗[𝕜] S.D) :
    S.τEquiv hB z = S.τ z := rfl

noncomputable def σ : A ⊗[𝕜] S.D →ₐ[𝕜] A :=
  Algebra.TensorProduct.lift (AlgHom.id 𝕜 A)
    ((Algebra.ofId 𝕜 A).comp ((Bialgebra.counitAlgHom 𝕜 (A ⊗[𝕜] B)).comp S.D.val))
    (fun _ _ => Commute.all _ _)

theorem σ_tmul (a : A) (d : S.D) :
    S.σ (a ⊗ₜ[𝕜] d) = a * algebraMap 𝕜 A (Coalgebra.counit (R := 𝕜) (d : A ⊗[𝕜] B)) := by
  simp [σ, Algebra.TensorProduct.lift_tmul, Algebra.ofId_apply]

noncomputable def ρ (hB : IsLocalRing (CartierDual 𝕜 B)) : A ⊗[𝕜] B →ₐ[𝕜] A :=
  S.σ.comp ((S.τEquiv hB).symm : A ⊗[𝕜] B →ₐ[𝕜] A ⊗[𝕜] S.D)

theorem ρ_tmul_one (hB : IsLocalRing (CartierDual 𝕜 B)) (a : A) : S.ρ hB (a ⊗ₜ[𝕜] 1) = a := by
  have h : (S.τEquiv hB).symm (a ⊗ₜ[𝕜] 1) = a ⊗ₜ[𝕜] (1 : S.D) := by
    apply (S.τEquiv hB).injective
    rw [AlgEquiv.apply_symm_apply, τEquiv_apply, τ_tmul]; simp
  rw [ρ, AlgHom.comp_apply, AlgEquiv.coe_algHom, h, σ_tmul]
  simp

theorem ρ_coe (hB : IsLocalRing (CartierDual 𝕜 B)) (d : S.D) :
    S.ρ hB (d : A ⊗[𝕜] B) = algebraMap 𝕜 A (Coalgebra.counit (R := 𝕜) (d : A ⊗[𝕜] B)) := by
  have h : (S.τEquiv hB).symm (d : A ⊗[𝕜] B) = (1 : A) ⊗ₜ[𝕜] d := by
    apply (S.τEquiv hB).injective
    rw [AlgEquiv.apply_symm_apply, τEquiv_apply, τ_tmul, ← Algebra.TensorProduct.one_def, one_mul]
  rw [ρ, AlgHom.comp_apply, AlgEquiv.coe_algHom, h, σ_tmul, one_mul]

noncomputable def g₀ (hB : IsLocalRing (CartierDual 𝕜 B)) : B →ₐ[𝕜] A :=
  (S.ρ hB).comp (Algebra.TensorProduct.includeRight : B →ₐ[𝕜] A ⊗[𝕜] B)

theorem map_g₀ (hB : IsLocalRing (CartierDual 𝕜 B)) (x : wittHom 𝕜 p S.N B) :
    TruncWitt.map (S.g₀ hB).toRingHom (x : TruncatedWittVector p S.N B) =
      (S.Y x : TruncatedWittVector p S.N A) := by
  have key : TruncWitt.map (Algebra.TensorProduct.includeRight : B →ₐ[𝕜] A ⊗[𝕜] B).toRingHom
      (x : TruncatedWittVector p S.N B) =
      TruncWitt.map (Algebra.TensorProduct.includeLeft : A →ₐ[𝕜] A ⊗[𝕜] B).toRingHom (S.Y x) -
        (S.Z x : TruncatedWittVector p S.N (A ⊗[𝕜] B)) := by
    rw [coe_Z]; abel
  have h := congrArg (TruncWitt.map (S.ρ hB).toRingHom) key
  rw [map_sub, TruncWitt.map_map, TruncWitt.map_map] at h
  have hl : (S.ρ hB).toRingHom.comp
      (Algebra.TensorProduct.includeLeft : A →ₐ[𝕜] A ⊗[𝕜] B).toRingHom = RingHom.id A :=
    RingHom.ext fun a => S.ρ_tmul_one hB a
  have hz : TruncWitt.map (S.ρ hB).toRingHom (S.Z x : TruncatedWittVector p S.N (A ⊗[𝕜] B)) = 0 := by
    refine TruncatedWittVector.ext fun i => ?_
    rw [TruncWitt.coeff_map, TruncatedWittVector.coeff_zero]
    change S.ρ hB _ = 0
    have hmem := S.coeff_Z_mem_D x i
    have := S.ρ_coe hB ⟨_, hmem⟩
    rw [Subtype.coe_mk] at this
    rw [this, counit_coeff_of_mem_wittHom (S.Z x).2 i, map_zero]
  rw [hl, TruncWitt.map_id, hz, sub_zero] at h
  exact h

theorem g₀_coeff (hB : IsLocalRing (CartierDual 𝕜 B)) (x : wittHom 𝕜 p S.N B) (i : Fin S.N) :
    S.g₀ hB ((x : TruncatedWittVector p S.N B).coeff i) =
      (S.Y x : TruncatedWittVector p S.N A).coeff i := by
  rw [← S.map_g₀ hB x, TruncWitt.coeff_map]; rfl

theorem counit_comp_g₀ (hB : IsLocalRing (CartierDual 𝕜 B)) :
    (Bialgebra.counitAlgHom 𝕜 A).comp (S.g₀ hB) = Bialgebra.counitAlgHom 𝕜 B := by
  refine AlgHom.ext_of_adjoin_eq_top
    (Deformation.adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual 𝕜 p B hB) ?_
  rintro _ ⟨n, x, i, rfl⟩
  obtain ⟨x', hx'⟩ := S.hN (of 𝕜 p B n x)
  rcases coeff_eq_zero_or_eq_coeff_of_of_eq x x' hx'.symm i with h0 | ⟨j, hj⟩
  · simp only [h0, map_zero]
  · rw [hj, AlgHom.comp_apply, g₀_coeff, Bialgebra.counitAlgHom_apply,
      Bialgebra.counitAlgHom_apply, counit_coeff_of_mem_wittHom (S.Y x').2,
      counit_coeff_of_mem_wittHom x'.2]

theorem map_comp_comul (hB : IsLocalRing (CartierDual 𝕜 B)) :
    (Algebra.TensorProduct.map (S.g₀ hB) (S.g₀ hB)).comp (Bialgebra.comulAlgHom 𝕜 B) =
      (Bialgebra.comulAlgHom 𝕜 A).comp (S.g₀ hB) := by
  refine AlgHom.ext_of_adjoin_eq_top
    (Deformation.adjoin_coeff_wittHom_eq_top_of_isLocalRing_cartierDual 𝕜 p B hB) ?_
  rintro _ ⟨n, x, i, rfl⟩
  obtain ⟨x', hx'⟩ := S.hN (of 𝕜 p B n x)
  rcases coeff_eq_zero_or_eq_coeff_of_of_eq x x' hx'.symm i with h0 | ⟨j, hj⟩
  · simp only [h0, map_zero]
  · rw [hj, AlgHom.comp_apply, AlgHom.comp_apply, g₀_coeff]

    set G : B ⊗[𝕜] B →+* A ⊗[𝕜] A := (Algebra.TensorProduct.map (S.g₀ hB) (S.g₀ hB)).toRingHom
    have hx := (mem_wittHom_iff (x' : TruncatedWittVector p S.N B)).1 x'.2
    have hy := (mem_wittHom_iff (S.Y x' : TruncatedWittVector p S.N A)).1 (S.Y x').2
    have h1 : Bialgebra.comulAlgHom 𝕜 B ((x' : TruncatedWittVector p S.N B).coeff j) =
        (TruncWitt.map (comulRingHom 𝕜 B) (x' : TruncatedWittVector p S.N B)).coeff j := by
      rw [TruncWitt.coeff_map]; rfl
    have h2 : Bialgebra.comulAlgHom 𝕜 A ((S.Y x' : TruncatedWittVector p S.N A).coeff j) =
        (TruncWitt.map (comulRingHom 𝕜 A) (S.Y x' : TruncatedWittVector p S.N A)).coeff j := by
      rw [TruncWitt.coeff_map]; rfl
    rw [h1, h2, hx, hy]
    change G _ = _
    rw [← TruncWitt.coeff_map G, map_add, TruncWitt.map_map, TruncWitt.map_map]
    have e1 : G.comp (Algebra.TensorProduct.includeLeft : B →ₐ[𝕜] B ⊗[𝕜] B).toRingHom =
        (Algebra.TensorProduct.includeLeft : A →ₐ[𝕜] A ⊗[𝕜] A).toRingHom.comp (S.g₀ hB).toRingHom :=
      RingHom.ext fun b => by simp [G]
    have e2 : G.comp (Algebra.TensorProduct.includeRight : B →ₐ[𝕜] B ⊗[𝕜] B).toRingHom =
        (Algebra.TensorProduct.includeRight : A →ₐ[𝕜] A ⊗[𝕜] A).toRingHom.comp (S.g₀ hB).toRingHom :=
      RingHom.ext fun b => by simp [G]
    rw [e1, e2, ← TruncWitt.map_map, ← TruncWitt.map_map, S.map_g₀ hB]

noncomputable def g (hB : IsLocalRing (CartierDual 𝕜 B)) : B →ₐc[𝕜] A :=
  BialgHom.ofAlgHom (S.g₀ hB) (S.counit_comp_g₀ hB) (S.map_comp_comul hB)

theorem map_g (hB : IsLocalRing (CartierDual 𝕜 B)) : DieudonneModule.map 𝕜 p (S.g hB) = S.φ := by
  refine hom_ext fun n x => ?_
  obtain ⟨x', hx'⟩ := S.hN (of 𝕜 p B n x)
  rw [← hx', map_of, ← of_Y]
  congr 1
  refine Subtype.ext ?_
  rw [coe_wittHomMap]
  exact S.map_g₀ hB x'

end Setup
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_map_eq_of_isLocalRing_cartierDual.DieudonneFull.Setup"

end Main
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_map_eq_of_isLocalRing_cartierDual.DieudonneFull.Setup"

end DieudonneFull
p2m_reactivate "P2MW.S_Deformation_DieudonneModule_exists_map_eq_of_isLocalRing_cartierDual.DieudonneFull.Setup P2MW.S_Deformation_DieudonneModule_exists_map_eq_of_isLocalRing_cartierDual.DieudonneFull"

open DieudonneFull in
theorem solution
    (p : ℕ) [Fact p.Prime]
    (A : Type u) [CommRing A] [Bialgebra (ZMod p) A] [Module.Finite (ZMod p) A]
    (B : Type v) [CommRing B] [HopfAlgebra (ZMod p) B] [Coalgebra.IsCocomm (ZMod p) B]
    [Module.Finite (ZMod p) B]
    (hB : IsLocalRing (CartierDual (ZMod p) B))
    (φ : Deformation.DieudonneModule (ZMod p) p B →+ Deformation.DieudonneModule (ZMod p) p A)
    (hF : ∀ z, φ (Deformation.DieudonneModule.frobenius (ZMod p) p B z) =
      Deformation.DieudonneModule.frobenius (ZMod p) p A (φ z))
    (hV : ∀ z, φ (Deformation.DieudonneModule.verschiebung (ZMod p) p B z) =
      Deformation.DieudonneModule.verschiebung (ZMod p) p A (φ z)) :
    ∃ g : B →ₐc[ZMod p] A, Deformation.DieudonneModule.map (ZMod p) p g = φ := by
  obtain ⟨N, hN⟩ := Deformation.DieudonneModule.exists_surjective_of (ZMod p) p B
  let S : Setup (p := p) (A := A) (B := B) := ⟨N, hN, φ, hF, hV⟩
  exact ⟨S.g hB, S.map_g hB⟩

end S_Deformation_DieudonneModule_exists_map_eq_of_isLocalRing_cartierDual
end P2MW
export P2MW.S_Deformation_DieudonneModule_exists_map_eq_of_isLocalRing_cartierDual (solution)
