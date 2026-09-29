-- Prove2me | solution 1 for CerednikDrinfeld.FormalOmega.DeligneDatum.exists_equiv_of_span_singleton_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.837917+00:00
-- url     : https://prove2.me/submissions/5ac01ceb-ad6e-5eae-b76c-297b65a8c45a

import Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneFunctor
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq

set_option autoImplicit false

noncomputable section

open scoped TensorProduct
p2m_open "LT.LatticeTree CerednikDrinfeld.FormalOmega P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega"
open Matrix

namespace CerednikDrinfeld
namespace FormalOmega
p2m_export "CerednikDrinfeld.FormalOmega" "transportEquiv transportEquiv_tmul coe_ofEq_apply DeligneDatum.line_transport coe_latticeMapEquiv_apply actBaseChange_tmul latticeBaseChange inclBaseChange latticeMapEquiv FullLattice.act actBaseChange DeligneDatum DeligneDatum.ext' DeligneDatum.IsPullback lineBaseChange DeligneDatum.IsBaseChange OmegaNrObj frobTwist OmegaNr.IsTwistedAct"
p2m_open "CerednikDrinfeld.FormalOmega CerednikDrinfeld"

section T0

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]

theorem smul_coe_mem_of_dvd {π π₂ : 𝒪} (hd : π ∣ π₂) {M' M : FullLattice 𝒪 K}
    (hπ : ∀ v : ↥M.1, (algebraMap 𝒪 K π) • (v : Fin 2 → K) ∈ M'.1) (v : ↥M.1) :
    (algebraMap 𝒪 K π₂) • (v : Fin 2 → K) ∈ M'.1 := by
  obtain ⟨a, rfl⟩ := hd
  have := hπ (a • v)
  rwa [Submodule.coe_smul, ← algebraMap_smul K a (v : Fin 2 → K), ← mul_smul, ← map_mul] at this

theorem exists_eq_smul_coe_of_dvd {π π₂ : 𝒪} (hd : π₂ ∣ π) {M' M : FullLattice 𝒪 K} (v' : ↥M'.1)
    (h : ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π) • (w : Fin 2 → K)) :
    ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π₂) • (w : Fin 2 → K) := by
  obtain ⟨a, rfl⟩ := hd
  obtain ⟨w, hw⟩ := h
  refine ⟨a • w, ?_⟩
  rw [hw, Submodule.coe_smul, ← algebraMap_smul K a (w : Fin 2 → K), ← mul_smul, ← map_mul]

namespace DeligneDatum p2m_export "CerednikDrinfeld.FormalOmega.DeligneDatum" "line_transport map ext' IsPullback IsBaseChange homothety mono invertible line nondeg" end DeligneDatum
namespace DeligneDatum
p2m_open_scoped "CerednikDrinfeld.FormalOmega.DeligneDatum" in

private theorem _root_.CerednikDrinfeld.FormalOmega.DeligneDatum.nondeg_of_dvd_of_dvd {π π₂ : 𝒪} (h₁ : π ∣ π₂) (h₂ : π₂ ∣ π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (d : DeligneDatum (K := K) π B) (𝔭 : Ideal B) (h𝔭 : 𝔭.IsPrime) :
    ∃ (M' M : FullLattice 𝒪 K) (_ : M'.1 ≤ M.1),
      (∀ v : ↥M.1, (algebraMap 𝒪 K π₂) • (v : Fin 2 → K) ∈ M'.1) ∧
      (∀ v : ↥M.1, (v : Fin 2 → K) ∉ M'.1 →
        (1 : B) ⊗ₜ[𝒪] v ∉ d.line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M))) ∧
      (∀ v' : ↥M'.1, (¬ ∃ w : ↥M.1, (v' : Fin 2 → K) = (algebraMap 𝒪 K π₂) • (w : Fin 2 → K)) →
        (1 : B) ⊗ₜ[𝒪] v' ∉ d.line M' ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M'))) := by
  obtain ⟨M', M, hle, hπM, hout, hprim⟩ := d.nondeg 𝔭 h𝔭
  refine ⟨M', M, hle, smul_coe_mem_of_dvd h₁ hπM, hout, fun v' hv' => hprim v' fun hex => hv' ?_⟩
  exact exists_eq_smul_coe_of_dvd h₂ v' hex

end DeligneDatum
p2m_export "CerednikDrinfeld.FormalOmega" "DeligneDatum.nondeg_of_dvd_of_dvd"
p2m_open_scoped "CerednikDrinfeld.FormalOmega.DeligneDatum" in

def DeligneDatum.changeUniformiser {π π₂ : 𝒪} (h₁ : π ∣ π₂) (h₂ : π₂ ∣ π)
    {B : Type} [CommRing B] [Algebra 𝒪 B] (d : DeligneDatum (K := K) π B) : DeligneDatum (K := K) π₂ B where
  line := d.line
  invertible := d.invertible
  mono := d.mono
  homothety := d.homothety
  nondeg := d.nondeg_of_dvd_of_dvd h₁ h₂

theorem dvd_of_span_singleton_eq {π π₂ : 𝒪} (h : Ideal.span {π} = Ideal.span {π₂}) : π ∣ π₂ := by
  rw [← Ideal.mem_span_singleton, h]; exact Ideal.mem_span_singleton_self π₂

p2m_open_scoped "CerednikDrinfeld.FormalOmega.DeligneDatum" in

def DeligneDatum.congrOfSpanEq {π π₂ : 𝒪} (h : Ideal.span {π} = Ideal.span {π₂})
    (B : Type) [CommRing B] [Algebra 𝒪 B] :
    DeligneDatum (K := K) π B ≃ DeligneDatum (K := K) π₂ B where
  toFun := DeligneDatum.changeUniformiser (dvd_of_span_singleton_eq h) (dvd_of_span_singleton_eq h.symm)
  invFun := DeligneDatum.changeUniformiser (dvd_of_span_singleton_eq h.symm) (dvd_of_span_singleton_eq h)
  left_inv d := DeligneDatum.ext' rfl
  right_inv d := DeligneDatum.ext' rfl

p2m_open_scoped "CerednikDrinfeld.FormalOmega.DeligneDatum" in
@[scoped simp] theorem DeligneDatum.congrOfSpanEq_line {π π₂ : 𝒪}
    (h : Ideal.span {π} = Ideal.span {π₂}) (B : Type) [CommRing B] [Algebra 𝒪 B] (d : DeligneDatum (K := K) π B) :
    (DeligneDatum.congrOfSpanEq (K := K) h B d).line = d.line := rfl

p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.DeligneDatum"
p2m_open_scoped "CerednikDrinfeld.FormalOmega.DeligneDatum" in

theorem DeligneDatum.isPullback_congrOfSpanEq_iff {π π₂ : 𝒪} (h : Ideal.span {π} = Ideal.span {π₂})
    (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K) (d d' : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K) (π := π₂) B g (DeligneDatum.congrOfSpanEq h B d) (DeligneDatum.congrOfSpanEq h B d') ↔
      DeligneDatum.IsPullback (K := K) (π := π) B g d d' := Iff.rfl

p2m_open_scoped "CerednikDrinfeld.FormalOmega.DeligneDatum" in

theorem DeligneDatum.isBaseChange_congrOfSpanEq_iff {π π₂ : 𝒪} (h : Ideal.span {π} = Ideal.span {π₂})
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
    (d : DeligneDatum (K := K) π B) (d' : DeligneDatum (K := K) π B') :
    DeligneDatum.IsBaseChange (K := K) (π := π₂) f (DeligneDatum.congrOfSpanEq h B d) (DeligneDatum.congrOfSpanEq h B' d') ↔
      DeligneDatum.IsBaseChange (K := K) (π := π) f d d' := Iff.rfl

end T0
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.DeligneDatum"

structure FrameIso (𝒪 : Type) [CommRing 𝒪] (K : Type) [Field K] [Algebra 𝒪 K]
    (𝒪' : Type) [CommRing 𝒪'] (K' : Type) [Field K'] [Algebra 𝒪' K'] : Type where
  base : 𝒪 ≃+* 𝒪'
  field : K ≃+* K'
  commutes : ∀ x : 𝒪, field (algebraMap 𝒪 K x) = algebraMap 𝒪' K' (base x)

namespace FrameIso

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {𝒪' : Type} [CommRing 𝒪'] {K' : Type} [Field K'] [Algebra 𝒪' K']

def symm (E : FrameIso 𝒪 K 𝒪' K') : FrameIso 𝒪' K' 𝒪 K where
  base := E.base.symm
  field := E.field.symm
  commutes x := by
    apply E.field.injective
    rw [RingEquiv.apply_symm_apply, E.commutes, RingEquiv.apply_symm_apply]

@[scoped simp] theorem symm_base (E : FrameIso 𝒪 K 𝒪' K') : E.symm.base = E.base.symm := rfl
@[scoped simp] theorem symm_field (E : FrameIso 𝒪 K 𝒪' K') : E.symm.field = E.field.symm := rfl

abbrev gl (E : FrameIso 𝒪 K 𝒪' K') : Matrix.GeneralLinearGroup (Fin 2) K →* Matrix.GeneralLinearGroup (Fin 2) K' :=
  Matrix.GeneralLinearGroup.map E.field.toRingHom

def vec (E : FrameIso 𝒪 K 𝒪' K') (v : Fin 2 → K) : Fin 2 → K' := fun i => E.field (v i)

@[scoped simp] theorem vec_apply (E : FrameIso 𝒪 K 𝒪' K') (v : Fin 2 → K) (i : Fin 2) : E.vec v i = E.field (v i) := rfl

theorem vec_add (E : FrameIso 𝒪 K 𝒪' K') (v w : Fin 2 → K) : E.vec (v + w) = E.vec v + E.vec w := by
  ext i; simp

@[scoped simp] theorem vec_zero (E : FrameIso 𝒪 K 𝒪' K') : E.vec 0 = 0 := by ext i; simp

theorem vec_smul (E : FrameIso 𝒪 K 𝒪' K') (r : 𝒪) (v : Fin 2 → K) : E.vec (r • v) = E.base r • E.vec v := by
  ext i; simp [Algebra.smul_def, E.commutes]

theorem vec_smulK (E : FrameIso 𝒪 K 𝒪' K') (c : K) (v : Fin 2 → K) : E.vec (c • v) = E.field c • E.vec v := by
  ext i; simp

@[scoped simp] theorem symm_vec_vec (E : FrameIso 𝒪 K 𝒪' K') (v : Fin 2 → K) : E.symm.vec (E.vec v) = v := by
  ext i; simp [vec, symm]

@[scoped simp] theorem vec_symm_vec (E : FrameIso 𝒪 K 𝒪' K') (w : Fin 2 → K') : E.vec (E.symm.vec w) = w := by
  ext i; simp [vec, symm]

theorem vec_mulVec (E : FrameIso 𝒪 K 𝒪' K') (g : Matrix.GeneralLinearGroup (Fin 2) K) (v : Fin 2 → K) :
    E.vec ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v) = ((E.gl g : Matrix.GeneralLinearGroup (Fin 2) K') : Matrix (Fin 2) (Fin 2) K') *ᵥ E.vec v := by
  ext i
  have hg : ∀ a b, ((E.gl g : Matrix.GeneralLinearGroup (Fin 2) K') : Matrix (Fin 2) (Fin 2) K') a b = E.field ((g : Matrix (Fin 2) (Fin 2) K) a b) :=
    fun a b => Matrix.GeneralLinearGroup.map_apply E.field.toRingHom a b g
  simp only [vec_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, hg]

def latticeSub (E : FrameIso 𝒪 K 𝒪' K') (L : Submodule 𝒪 (Fin 2 → K)) : Submodule 𝒪' (Fin 2 → K') where
  carrier := E.vec '' (L : Set (Fin 2 → K))
  zero_mem' := ⟨0, L.zero_mem, E.vec_zero⟩
  add_mem' := by
    rintro _ _ ⟨v, hv, rfl⟩ ⟨w, hw, rfl⟩
    exact ⟨v + w, L.add_mem hv hw, E.vec_add v w⟩
  smul_mem' := by
    rintro c _ ⟨v, hv, rfl⟩
    refine ⟨E.base.symm c • v, L.smul_mem _ hv, ?_⟩
    rw [E.vec_smul, RingEquiv.apply_symm_apply]

theorem mem_latticeSub_iff (E : FrameIso 𝒪 K 𝒪' K') (L : Submodule 𝒪 (Fin 2 → K)) (w : Fin 2 → K') :
    w ∈ E.latticeSub L ↔ ∃ v ∈ L, E.vec v = w := Iff.rfl

theorem vec_mem_latticeSub (E : FrameIso 𝒪 K 𝒪' K') {L : Submodule 𝒪 (Fin 2 → K)} {v : Fin 2 → K} (hv : v ∈ L) :
    E.vec v ∈ E.latticeSub L := ⟨v, hv, rfl⟩

theorem vec_mem_latticeSub_iff (E : FrameIso 𝒪 K 𝒪' K') {L : Submodule 𝒪 (Fin 2 → K)} {v : Fin 2 → K} :
    E.vec v ∈ E.latticeSub L ↔ v ∈ L := by
  refine ⟨?_, E.vec_mem_latticeSub⟩
  rintro ⟨w, hw, hwv⟩
  have : w = v := by simpa using congrArg E.symm.vec hwv
  exact this ▸ hw

@[scoped simp] theorem latticeSub_symm_latticeSub (E : FrameIso 𝒪 K 𝒪' K') (L : Submodule 𝒪 (Fin 2 → K)) :
    E.symm.latticeSub (E.latticeSub L) = L := by
  ext v
  constructor
  · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩
    simpa using hu
  · intro hv
    exact ⟨E.vec v, ⟨v, hv, rfl⟩, E.symm_vec_vec v⟩

@[scoped simp] theorem symm_latticeSub_latticeSub (E : FrameIso 𝒪 K 𝒪' K') (L : Submodule 𝒪' (Fin 2 → K')) :
    E.latticeSub (E.symm.latticeSub L) = L := by
  ext w
  constructor
  · rintro ⟨v, ⟨u, hu, rfl⟩, rfl⟩
    simpa using hu
  · intro hw
    exact ⟨E.symm.vec w, ⟨w, hw, rfl⟩, E.vec_symm_vec w⟩

theorem isFullLattice_latticeSub (E : FrameIso 𝒪 K 𝒪' K') {L : Submodule 𝒪 (Fin 2 → K)} (hL : IsFullLattice L) :
    IsFullLattice (E.latticeSub L) := by
  classical
  constructor
  · obtain ⟨s, hs⟩ := hL.1
    refine ⟨s.image E.vec, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      rintro _ hw
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp (Finset.mem_coe.mp hw)
      exact E.vec_mem_latticeSub (hs ▸ Submodule.subset_span hv)
    · rintro _ ⟨v, hv, rfl⟩
      rw [← hs] at hv
      induction hv using Submodule.span_induction with
      | mem u hu => exact Submodule.subset_span (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨u, hu, rfl⟩))
      | zero => simp
      | add u w _ _ hu hw => rw [E.vec_add]; exact Submodule.add_mem _ hu hw
      | smul r u _ hu => rw [E.vec_smul]; exact Submodule.smul_mem _ _ hu
  · rw [eq_top_iff]
    intro w _
    have hv : E.symm.vec w ∈ Submodule.span K (L : Set (Fin 2 → K)) := hL.2 ▸ Submodule.mem_top
    rw [← E.vec_symm_vec w]
    suffices h : ∀ v, v ∈ Submodule.span K (L : Set (Fin 2 → K)) →
        E.vec v ∈ Submodule.span K' (E.latticeSub L : Set (Fin 2 → K')) from h _ hv
    intro v hv
    induction hv using Submodule.span_induction with
    | mem u hu => exact Submodule.subset_span ⟨u, hu, rfl⟩
    | zero => simp
    | add u u' _ _ hu hu' => rw [E.vec_add]; exact Submodule.add_mem _ hu hu'
    | smul c u _ hu => rw [E.vec_smulK]; exact Submodule.smul_mem _ _ hu

def lattice (E : FrameIso 𝒪 K 𝒪' K') : FullLattice 𝒪 K ≃ FullLattice 𝒪' K' where
  toFun M := ⟨E.latticeSub M.1, E.isFullLattice_latticeSub M.2⟩
  invFun N := ⟨E.symm.latticeSub N.1, E.symm.isFullLattice_latticeSub N.2⟩
  left_inv M := Subtype.ext (E.latticeSub_symm_latticeSub M.1)
  right_inv N := Subtype.ext (E.symm_latticeSub_latticeSub N.1)

@[scoped simp] theorem lattice_val (E : FrameIso 𝒪 K 𝒪' K') (M : FullLattice 𝒪 K) : (E.lattice M).1 = E.latticeSub M.1 := rfl
@[scoped simp] theorem lattice_symm_val (E : FrameIso 𝒪 K 𝒪' K') (N : FullLattice 𝒪' K') :
    ((E.lattice).symm N).1 = E.symm.latticeSub N.1 := rfl

theorem mem_lattice_iff (E : FrameIso 𝒪 K 𝒪' K') (M : FullLattice 𝒪 K) (w : Fin 2 → K') :
    w ∈ (E.lattice M).1 ↔ ∃ v ∈ M.1, E.vec v = w := Iff.rfl

theorem vec_mem_lattice (E : FrameIso 𝒪 K 𝒪' K') (M : FullLattice 𝒪 K) (v : ↥M.1) : E.vec v ∈ (E.lattice M).1 :=
  ⟨v, v.2, rfl⟩

theorem latticeSub_latticeMap (E : FrameIso 𝒪 K 𝒪' K') (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (L : Submodule 𝒪 (Fin 2 → K)) : E.latticeSub (latticeMap g L) = latticeMap (E.gl g) (E.latticeSub L) := by
  ext w
  simp only [mem_latticeSub_iff, mem_latticeMap]
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨E.vec u, ⟨u, hu, rfl⟩, (E.vec_mulVec g u).symm⟩
  · rintro ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact ⟨_, ⟨u, hu, rfl⟩, E.vec_mulVec g u⟩

theorem lattice_act (E : FrameIso 𝒪 K 𝒪' K') (g : Matrix.GeneralLinearGroup (Fin 2) K) (M : FullLattice 𝒪 K) :
    E.lattice (FullLattice.act g M) = FullLattice.act (E.gl g) (E.lattice M) :=
  Subtype.ext (E.latticeSub_latticeMap g M.1)

def coeff (E : FrameIso 𝒪 K 𝒪' K')
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Onr' : Type) [CommRing Onr'] [Algebra 𝒪' Onr']
    (eO : Onr ≃+* Onr') (heO : ∀ x : 𝒪, eO (algebraMap 𝒪 Onr x) = algebraMap 𝒪' Onr' (E.base x))
    (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) :
    (Onr →ₐ[𝒪] B) ≃ (Onr' →ₐ[𝒪'] B) where
  toFun ψ :=
    { toRingHom := ψ.toRingHom.comp eO.symm.toRingHom
      commutes' := fun r' => by
        obtain ⟨r, rfl⟩ := E.base.surjective r'
        show ψ (eO.symm (algebraMap 𝒪' Onr' (E.base r))) = algebraMap 𝒪' B (E.base r)
        rw [← heO, RingEquiv.symm_apply_apply, ψ.commutes, hB] }
  invFun ψ' :=
    { toRingHom := ψ'.toRingHom.comp eO.toRingHom
      commutes' := fun r => by
        show ψ' (eO (algebraMap 𝒪 Onr r)) = algebraMap 𝒪 B r
        rw [heO, ψ'.commutes, hB] }
  left_inv ψ := AlgHom.ext fun y => by
    show ψ (eO.symm (eO y)) = ψ y
    rw [RingEquiv.symm_apply_apply]
  right_inv ψ' := AlgHom.ext fun y => by
    show ψ' (eO (eO.symm y)) = ψ' y
    rw [RingEquiv.apply_symm_apply]

theorem coeff_apply (E : FrameIso 𝒪 K 𝒪' K')
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Onr' : Type) [CommRing Onr'] [Algebra 𝒪' Onr']
    (eO : Onr ≃+* Onr') (heO : ∀ x : 𝒪, eO (algebraMap 𝒪 Onr x) = algebraMap 𝒪' Onr' (E.base x))
    (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) (ψ : Onr →ₐ[𝒪] B) (y : Onr') :
    E.coeff Onr Onr' eO heO B hB ψ y = ψ (eO.symm y) := rfl

theorem map_frobPow (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (Onr' : Type) [CommRing Onr'] [Algebra 𝒪' Onr'] (Fr' : Onr' ≃ₐ[𝒪'] Onr')
    (eO : Onr ≃+* Onr') (hFr : ∀ y, eO (Fr y) = Fr' (eO y)) :
    ∀ (n : ℤ) (y : Onr), eO ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) y) = (Fr' ^ n : Onr' ≃ₐ[𝒪'] Onr') (eO y) := by
  have hnat : ∀ (n : ℕ) (y : Onr), eO ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) y) = (Fr' ^ n : Onr' ≃ₐ[𝒪'] Onr') (eO y) := by
    intro n
    induction n with
    | zero => intro y; rfl
    | succ n ih => intro y; rw [pow_succ, pow_succ, AlgEquiv.mul_apply, AlgEquiv.mul_apply, ← hFr, ih]
  intro n
  cases n with
  | ofNat n => intro y; exact_mod_cast hnat n y
  | negSucc n =>
      intro y
      rw [zpow_negSucc, zpow_negSucc, AlgEquiv.aut_inv, AlgEquiv.aut_inv]
      apply (Fr' ^ (n + 1) : Onr' ≃ₐ[𝒪'] Onr').injective
      rw [AlgEquiv.apply_symm_apply, ← hnat, AlgEquiv.apply_symm_apply]

theorem coeff_frobTwist (E : FrameIso 𝒪 K 𝒪' K')
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (Onr' : Type) [CommRing Onr'] [Algebra 𝒪' Onr'] (Fr' : Onr' ≃ₐ[𝒪'] Onr')
    (eO : Onr ≃+* Onr') (heO : ∀ x : 𝒪, eO (algebraMap 𝒪 Onr x) = algebraMap 𝒪' Onr' (E.base x))
    (hFr : ∀ y, eO (Fr y) = Fr' (eO y))
    (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) (n : ℤ) (ψ : Onr →ₐ[𝒪] B) :
    E.coeff Onr Onr' eO heO B hB (frobTwist Onr Fr n ψ) = frobTwist Onr' Fr' n (E.coeff Onr Onr' eO heO B hB ψ) := by
  apply AlgHom.ext
  intro y
  show ψ ((Fr ^ n : Onr ≃ₐ[𝒪] Onr) (eO.symm y)) = ψ (eO.symm ((Fr' ^ n : Onr' ≃ₐ[𝒪'] Onr') y))
  congr 1
  apply eO.injective
  rw [map_frobPow Onr Fr Onr' Fr' eO hFr, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]

end FrameIso
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.DeligneDatum P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso"

namespace FrameIso

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {𝒪' : Type} [CommRing 𝒪'] {K' : Type} [Field K'] [Algebra 𝒪' K']

def Twist (E : FrameIso 𝒪 K 𝒪' K') (P : Type) : Type := P

namespace Twist

variable (E : FrameIso 𝒪 K 𝒪' K') (P : Type)

scoped instance [i : AddCommGroup P] : AddCommGroup (Twist E P) := i
scoped instance instModule' [AddCommGroup P] [i : Module 𝒪' P] : Module 𝒪' (Twist E P) := i

scoped instance instModule [AddCommGroup P] [Module 𝒪' P] : Module 𝒪 (Twist E P) :=
  Module.compHom P (E.base : 𝒪 →+* 𝒪')

def out [AddCommGroup P] [Module 𝒪' P] : Twist E P ≃ₗ[𝒪'] P := LinearEquiv.refl 𝒪' P

def into [AddCommGroup P] [Module 𝒪' P] : P → Twist E P := fun p => p

theorem base_smul [AddCommGroup P] [Module 𝒪' P] (r : 𝒪) (p : Twist E P) :
    (E.base r) • p = r • p := rfl

end Twist
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.DeligneDatum P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso.Twist"

def latticeEquiv (E : FrameIso 𝒪 K 𝒪' K') (M : FullLattice 𝒪 K) : ↥M.1 ≃ₗ[𝒪] Twist E ↥(E.lattice M).1 where
  toFun v := Twist.into E _ ⟨E.vec v, E.vec_mem_lattice M v⟩
  map_add' v w := by
    apply (Twist.out E _).injective
    exact Subtype.ext (E.vec_add v w)
  map_smul' r v := by
    apply (Twist.out E _).injective
    exact Subtype.ext (E.vec_smul r v)
  invFun w := ⟨E.symm.vec (Twist.out E _ w : ↥(E.lattice M).1),
    (E.vec_mem_latticeSub_iff).mp (by rw [E.vec_symm_vec]; exact (Twist.out E _ w).2)⟩
  left_inv v := Subtype.ext (E.symm_vec_vec v)
  right_inv w := by
    apply (Twist.out E _).injective
    exact Subtype.ext (E.vec_symm_vec _)

theorem latticeEquiv_apply_coe (E : FrameIso 𝒪 K 𝒪' K') (M : FullLattice 𝒪 K) (v : ↥M.1) :
    ((Twist.out E _ (E.latticeEquiv M v) : ↥(E.lattice M).1) : Fin 2 → K') = E.vec v := rfl

theorem smulCommClass_base (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B] : SMulCommClass 𝒪 𝒪' B :=
  ⟨fun r r' b => by simp only [Algebra.smul_def]; ring⟩

theorem compatibleSMul₁ (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) (P : Type) [AddCommGroup P] [Module 𝒪' P] :
    TensorProduct.CompatibleSMul 𝒪 𝒪' B (Twist E P) :=
  ⟨fun r' b p => by
    obtain ⟨r, rfl⟩ := E.base.surjective r'
    have : E.base r • b = r • b := by rw [Algebra.smul_def, Algebra.smul_def, hB]
    rw [this, Twist.base_smul, TensorProduct.smul_tmul, TensorProduct.tmul_smul]⟩

theorem compatibleSMul₂ (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) (P : Type) [AddCommGroup P] [Module 𝒪' P] :
    TensorProduct.CompatibleSMul 𝒪' 𝒪 B (Twist E P) :=
  ⟨fun r b p => by
    have : r • b = E.base r • b := by rw [Algebra.smul_def, Algebra.smul_def, hB]
    rw [this, ← Twist.base_smul, TensorProduct.smul_tmul, TensorProduct.tmul_smul]⟩

def untwist (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) (P : Type) [AddCommGroup P] [Module 𝒪' P] :
    B ⊗[𝒪'] Twist E P ≃ₗ[B] B ⊗[𝒪] Twist E P :=
  haveI := smulCommClass_base (𝒪 := 𝒪) (𝒪' := 𝒪') B
  haveI := E.compatibleSMul₁ B hB P
  haveI := E.compatibleSMul₂ B hB P
  TensorProduct.equivOfCompatibleSMul 𝒪 𝒪' B B (Twist E P)

theorem untwist_tmul (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) (P : Type) [AddCommGroup P] [Module 𝒪' P]
    (b : B) (p : Twist E P) :
    E.untwist B hB P (b ⊗ₜ[𝒪'] p) = b ⊗ₜ[𝒪] p := rfl

def tensor (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) (M : FullLattice 𝒪 K) :
    latticeBaseChange 𝒪 K B M ≃ₗ[B] latticeBaseChange 𝒪' K' B (E.lattice M) :=
  (E.latticeEquiv M).baseChange 𝒪 B _ _ ≪≫ₗ (E.untwist B hB _).symm ≪≫ₗ
    (Twist.out E ↥(E.lattice M).1).baseChange 𝒪' B _ _

theorem tensor_tmul (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) (M : FullLattice 𝒪 K) (b : B) (v : ↥M.1) :
    E.tensor B hB M (b ⊗ₜ[𝒪] v) = b ⊗ₜ[𝒪'] (⟨E.vec v, E.vec_mem_lattice M v⟩ : ↥(E.lattice M).1) := by
  show (Twist.out E ↥(E.lattice M).1).baseChange 𝒪' B _ _
      ((E.untwist B hB _).symm ((E.latticeEquiv M).baseChange 𝒪 B _ _ (b ⊗ₜ[𝒪] v))) = _
  rw [LinearEquiv.baseChange_tmul]
  have h1 : (E.untwist B hB _).symm (b ⊗ₜ[𝒪] (E.latticeEquiv M v)) = b ⊗ₜ[𝒪'] (E.latticeEquiv M v) := rfl
  rw [h1, LinearEquiv.baseChange_tmul]
  rfl

end FrameIso
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.DeligneDatum P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso.Twist"

namespace FrameIso

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {𝒪' : Type} [CommRing 𝒪'] {K' : Type} [Field K'] [Algebra 𝒪' K']

theorem symm_compat (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) :
    ∀ x' : 𝒪', algebraMap 𝒪' B x' = algebraMap 𝒪 B (E.symm.base x') := fun x' => by
  rw [symm_base, hB, RingEquiv.apply_symm_apply]

theorem latticeSub_mono (E : FrameIso 𝒪 K 𝒪' K') {L' L : Submodule 𝒪 (Fin 2 → K)} (h : L' ≤ L) :
    E.latticeSub L' ≤ E.latticeSub L := by
  rintro _ ⟨v, hv, rfl⟩; exact ⟨v, h hv, rfl⟩

theorem latticeSub_le_iff (E : FrameIso 𝒪 K 𝒪' K') {L' L : Submodule 𝒪 (Fin 2 → K)} :
    E.latticeSub L' ≤ E.latticeSub L ↔ L' ≤ L := by
  refine ⟨fun h v hv => ?_, E.latticeSub_mono⟩
  exact E.vec_mem_latticeSub_iff.mp (h (E.vec_mem_latticeSub hv))

theorem symm_vec_mem_of_mem_lattice (E : FrameIso 𝒪 K 𝒪' K') (M : FullLattice 𝒪 K) {w : Fin 2 → K'}
    (hw : w ∈ (E.lattice M).1) : E.symm.vec w ∈ M.1 := by
  obtain ⟨v, hv, rfl⟩ := hw; simpa using hv

theorem gl_scalarGL (E : FrameIso 𝒪 K 𝒪' K') (c : Kˣ) :
    E.gl (scalarGL c) = scalarGL (Units.map (E.field : K →* K') c) := by
  apply Units.ext
  ext i j
  rw [Matrix.GeneralLinearGroup.map_apply]
  simp [scalarGL, Matrix.smul_apply, Matrix.one_apply]
  split_ifs <;> simp

theorem tensor_inclBaseChange (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) {M' M : FullLattice 𝒪 K} (h : M'.1 ≤ M.1)
    (x : latticeBaseChange 𝒪 K B M') :
    E.tensor B hB M (inclBaseChange B h x) =
      inclBaseChange B (show (E.lattice M').1 ≤ (E.lattice M).1 from E.latticeSub_mono h) (E.tensor B hB M' x) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearMap.map_zero, LinearEquiv.map_zero, LinearEquiv.map_zero, LinearMap.map_zero]
  | add x y hx hy => rw [LinearMap.map_add, LinearEquiv.map_add, LinearEquiv.map_add, LinearMap.map_add, hx, hy]
  | tmul b v =>
      show E.tensor B hB M (b ⊗ₜ[𝒪] Submodule.inclusion h v) = inclBaseChange B _ (E.tensor B hB M' (b ⊗ₜ[𝒪] v))
      rw [tensor_tmul, tensor_tmul]
      rfl

theorem map_smul_top {B : Type} [CommRing B] {X Y : Type} [AddCommGroup X] [Module B X] [AddCommGroup Y] [Module B Y]
    (Φ : X ≃ₗ[B] Y) (𝔭 : Ideal B) :
    (𝔭 • ⊤ : Submodule B X).map Φ.toLinearMap = (𝔭 • ⊤ : Submodule B Y) := by
  rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]

theorem mem_sup_smul_top_iff {B : Type} [CommRing B] {X Y : Type} [AddCommGroup X] [Module B X] [AddCommGroup Y]
    [Module B Y] (Φ : X ≃ₗ[B] Y) (P : Submodule B X) (𝔭 : Ideal B) (x : X) :
    x ∈ P ⊔ (𝔭 • ⊤ : Submodule B X) ↔ Φ x ∈ P.map Φ.toLinearMap ⊔ (𝔭 • ⊤ : Submodule B Y) := by
  rw [← map_smul_top Φ 𝔭, ← Submodule.map_sup]
  constructor
  · exact fun hx => Submodule.mem_map_of_mem hx
  · rintro ⟨y, hy, hyx⟩
    rwa [← Φ.injective hyx]

theorem tensor_actBaseChange (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) (g : Matrix.GeneralLinearGroup (Fin 2) K)
    (M : FullLattice 𝒪 K) (x : latticeBaseChange 𝒪 K B M) :
    E.tensor B hB (FullLattice.act g M) (actBaseChange B g M x) =
      transportEquiv B (congrArg Subtype.val (E.lattice_act g M)).symm
        (actBaseChange B (E.gl g) (E.lattice M) (E.tensor B hB M x)) := by
  induction x using TensorProduct.induction_on with
  | zero => rw [LinearEquiv.map_zero, LinearEquiv.map_zero, LinearEquiv.map_zero, LinearEquiv.map_zero,
      LinearEquiv.map_zero]
  | add x y hx hy => rw [LinearEquiv.map_add, LinearEquiv.map_add, LinearEquiv.map_add, LinearEquiv.map_add,
      LinearEquiv.map_add, hx, hy]
  | tmul b v =>
      rw [actBaseChange_tmul, tensor_tmul]
      refine (E.tensor_tmul B hB (FullLattice.act g M) b _).trans ?_
      rw [actBaseChange_tmul]
      refine Eq.trans ?_ (transportEquiv_tmul B _ b _).symm
      congr 1
      apply Subtype.ext
      show E.vec ((latticeMapEquiv g M.1 v : ↥(latticeMap g M.1)) : Fin 2 → K) = _
      rw [coe_ofEq_apply, coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, vec_mulVec]

section Transport

variable (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
  (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x))

def τ (N : FullLattice 𝒪' K') : latticeBaseChange 𝒪' K' B N ≃ₗ[B] latticeBaseChange 𝒪 K B (E.symm.lattice N) :=
  E.symm.tensor B (E.symm_compat B hB) N

theorem τ_tmul (N : FullLattice 𝒪' K') (b : B) (w : ↥N.1) :
    E.τ B hB N (b ⊗ₜ[𝒪'] w) = b ⊗ₜ[𝒪] (⟨E.symm.vec w, E.symm.vec_mem_lattice N w⟩ : ↥(E.symm.lattice N).1) :=
  E.symm.tensor_tmul B (E.symm_compat B hB) N b w

include hB in

def transport {π : 𝒪} {π' : 𝒪'} (hπ : E.base π = π') (d : DeligneDatum (K := K) π B) :
    DeligneDatum (K := K') π' B where
  line N := (d.line (E.symm.lattice N)).comap (E.τ B hB N).toLinearMap
  invertible N := by
    haveI := d.invertible (E.symm.lattice N)
    exact Module.Invertible.congr
      (Submodule.Quotient.equiv ((d.line (E.symm.lattice N)).comap (E.τ B hB N).toLinearMap)
        (d.line (E.symm.lattice N)) (E.τ B hB N)
        (Submodule.map_comap_eq_of_surjective (E.τ B hB N).surjective _)).symm
  mono {N' N} h := by
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearEquiv.coe_coe] at hx
    rw [Submodule.mem_comap, LinearEquiv.coe_coe]
    have h₀ : (E.symm.lattice N').1 ≤ (E.symm.lattice N).1 := E.symm.latticeSub_mono h
    have := E.symm.tensor_inclBaseChange B (E.symm_compat B hB) h x
    change E.symm.tensor B (E.symm_compat B hB) N (inclBaseChange B h x) ∈ d.line (E.symm.lattice N)
    rw [this]
    exact d.mono h₀ (Submodule.mem_map_of_mem hx)
  homothety c' N := by

    let c : Kˣ := Units.map (E.symm.field : K' →* K) c'
    have hidx : (FullLattice.act (scalarGL c) (E.symm.lattice N)).1 =
        (E.symm.lattice (FullLattice.act (scalarGL c') N)).1 := by
      rw [E.symm.lattice_act, E.symm.gl_scalarGL]

    have K1 : ∀ x : latticeBaseChange 𝒪' K' B N,
        E.τ B hB (FullLattice.act (scalarGL c') N) (actBaseChange B (scalarGL c') N x) =
          transportEquiv B hidx (actBaseChange B (scalarGL c) (E.symm.lattice N) (E.τ B hB N x)) := by
      intro x
      have h := E.symm.tensor_actBaseChange B (E.symm_compat B hB) (scalarGL c') N x
      rw [show E.τ B hB (FullLattice.act (scalarGL c') N) = E.symm.tensor B (E.symm_compat B hB) _ from rfl, h]

      rw [show E.τ B hB N = E.symm.tensor B (E.symm_compat B hB) N from rfl]
      generalize E.symm.tensor B (E.symm_compat B hB) N x = y
      induction y using TensorProduct.induction_on with
      | zero => simp only [LinearEquiv.map_zero]
      | add y z hy hz => simp only [LinearEquiv.map_add, hy, hz]
      | tmul b w =>
          rw [actBaseChange_tmul, actBaseChange_tmul]
          erw [transportEquiv_tmul, transportEquiv_tmul]
          congr 1
          apply Subtype.ext
          rw [coe_ofEq_apply, coe_ofEq_apply, coe_latticeMapEquiv_apply, coe_latticeMapEquiv_apply, E.symm.gl_scalarGL]
    show (d.line (E.symm.lattice (FullLattice.act (scalarGL c') N))).comap
        (E.τ B hB (FullLattice.act (scalarGL c') N)).toLinearMap =
      ((d.line (E.symm.lattice N)).comap (E.τ B hB N).toLinearMap).map (actBaseChange B (scalarGL c') N).toLinearMap
    rw [DeligneDatum.line_transport π d hidx, d.homothety c (E.symm.lattice N)]
    ext x
    simp only [Submodule.mem_comap, Submodule.mem_map, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, hyx⟩
      refine ⟨(actBaseChange B (scalarGL c') N).symm x, ?_, LinearEquiv.apply_symm_apply _ _⟩
      have e1 := K1 ((actBaseChange B (scalarGL c') N).symm x)
      rw [LinearEquiv.apply_symm_apply] at e1
      rw [e1] at hyx
      have : y = E.τ B hB N ((actBaseChange B (scalarGL c') N).symm x) :=
        (actBaseChange B (scalarGL c) (E.symm.lattice N)).injective ((transportEquiv B hidx).injective hyx)
      rw [← this]; exact hy
    · rintro ⟨z, hz, rfl⟩
      exact ⟨_, ⟨E.τ B hB N z, hz, rfl⟩, (K1 z).symm⟩
  nondeg 𝔭 h𝔭 := by
    obtain ⟨M₀', M₀, hle, hπ0, h1, h2⟩ := d.nondeg 𝔭 h𝔭

    have transfer : ∀ (M : FullLattice 𝒪 K) (w : ↥(E.lattice M).1),
        (1 : B) ⊗ₜ[𝒪'] w ∈ (d.line (E.symm.lattice (E.lattice M))).comap (E.τ B hB (E.lattice M)).toLinearMap ⊔
            (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪' K' B (E.lattice M))) →
        (1 : B) ⊗ₜ[𝒪] (⟨E.symm.vec w, E.symm_vec_mem_of_mem_lattice M w.2⟩ : ↥M.1) ∈
          d.line M ⊔ (𝔭 • ⊤ : Submodule B (latticeBaseChange 𝒪 K B M)) := by
      intro M w hw
      have hM : (E.symm.lattice (E.lattice M)).1 = M.1 := E.latticeSub_symm_latticeSub M.1
      rw [mem_sup_smul_top_iff (E.τ B hB (E.lattice M)), Submodule.map_comap_eq_of_surjective
        (E.τ B hB (E.lattice M)).surjective, τ_tmul, mem_sup_smul_top_iff (transportEquiv B hM),
        ← DeligneDatum.line_transport π d hM, transportEquiv_tmul] at hw
      exact hw
    refine ⟨E.lattice M₀', E.lattice M₀, E.latticeSub_mono hle, ?_, ?_, ?_⟩
    · intro w
      obtain ⟨u, hu, hw⟩ := w.2
      rw [← hw, ← hπ, algebraMap_smul, ← E.vec_smul]
      have := hπ0 ⟨u, hu⟩
      rw [algebraMap_smul] at this
      exact E.vec_mem_latticeSub this
    · intro w hw hmem
      refine h1 ⟨E.symm.vec w, E.symm_vec_mem_of_mem_lattice M₀ w.2⟩ ?_ (transfer M₀ w hmem)
      intro hv
      apply hw
      have := E.vec_mem_latticeSub hv
      rwa [vec_symm_vec] at this
    · intro w' hw' hmem
      refine h2 ⟨E.symm.vec w', E.symm_vec_mem_of_mem_lattice M₀' w'.2⟩ ?_ (transfer M₀' w' hmem)
      rintro ⟨v₀, hv₀⟩
      apply hw'
      refine ⟨⟨E.vec v₀, E.vec_mem_lattice M₀ v₀⟩, ?_⟩
      have := congrArg E.vec hv₀
      rw [vec_symm_vec, E.vec_smulK, E.commutes, hπ] at this
      exact this

end Transport
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.DeligneDatum P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso.Twist"

end FrameIso
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.DeligneDatum P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso.Twist"

namespace FrameIso

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {𝒪' : Type} [CommRing 𝒪'] {K' : Type} [Field K'] [Algebra 𝒪' K']

theorem symm_hπ (E : FrameIso 𝒪 K 𝒪' K') {π : 𝒪} {π' : 𝒪'} (hπ : E.base π = π') : E.symm.base π' = π := by
  rw [symm_base, ← hπ, RingEquiv.symm_apply_apply]

theorem τ_τ (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) (M : FullLattice 𝒪 K)
    (x : latticeBaseChange 𝒪 K B M) :
    E.τ B hB (E.symm.symm.lattice M) (E.symm.τ B (E.symm_compat B hB) M x) =
      transportEquiv B (E.symm.symm_latticeSub_latticeSub M.1).symm x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero]
  | add x y hx hy => simp only [LinearEquiv.map_add, hx, hy]
  | tmul b v =>
      rw [τ_tmul, τ_tmul]
      refine Eq.trans ?_ (transportEquiv_tmul B _ b v).symm
      congr 1
      apply Subtype.ext
      exact E.symm.vec_symm_vec v

theorem transport_transport (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) {π : 𝒪} {π' : 𝒪'} (hπ : E.base π = π')
    (d : DeligneDatum (K := K) π B) :
    E.symm.transport B (E.symm_compat B hB) (E.symm_hπ hπ) (E.transport B hB hπ d) = d := by
  apply DeligneDatum.ext'
  funext M
  ext x
  show E.τ B hB (E.symm.symm.lattice M) (E.symm.τ B (E.symm_compat B hB) M x) ∈
      d.line (E.symm.lattice (E.symm.symm.lattice M)) ↔ x ∈ d.line M
  rw [τ_τ, DeligneDatum.line_transport π d (E.symm.symm_latticeSub_latticeSub M.1).symm, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rwa [← (transportEquiv B _).injective hyx]
  · exact fun hx => ⟨x, hx, rfl⟩

def deligne (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) {π : 𝒪} {π' : 𝒪'} (hπ : E.base π = π') :
    DeligneDatum (K := K) π B ≃ DeligneDatum (K := K') π' B where
  toFun := E.transport B hB hπ
  invFun := E.symm.transport B (E.symm_compat B hB) (E.symm_hπ hπ)
  left_inv := E.transport_transport B hB hπ
  right_inv := E.symm.transport_transport B (E.symm_compat B hB) (E.symm_hπ hπ)

theorem deligne_apply_line (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) {π : 𝒪} {π' : 𝒪'} (hπ : E.base π = π')
    (d : DeligneDatum (K := K) π B) (N : FullLattice 𝒪' K') :
    (E.deligne B hB hπ d).line N = (d.line (E.symm.lattice N)).comap (E.τ B hB N).toLinearMap := rfl

theorem τ_tensor (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) (M : FullLattice 𝒪 K)
    (x : latticeBaseChange 𝒪 K B M) :
    E.τ B hB (E.lattice M) (E.tensor B hB M x) = transportEquiv B (E.latticeSub_symm_latticeSub M.1).symm x := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [LinearEquiv.map_zero]
  | add x y hx hy => simp only [LinearEquiv.map_add, hx, hy]
  | tmul b v =>
      rw [tensor_tmul, τ_tmul]
      refine Eq.trans ?_ (transportEquiv_tmul B _ b v).symm
      congr 1
      apply Subtype.ext
      exact E.symm_vec_vec v

theorem deligne_line (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) {π : 𝒪} {π' : 𝒪'} (hπ : E.base π = π')
    (d : DeligneDatum (K := K) π B) (M : FullLattice 𝒪 K) :
    (E.deligne B hB hπ d).line (E.lattice M) = (d.line M).map (E.tensor B hB M).toLinearMap := by
  rw [deligne_apply_line, DeligneDatum.line_transport π d (E.latticeSub_symm_latticeSub M.1).symm]
  ext x
  obtain ⟨y, rfl⟩ := (E.tensor B hB M).surjective x
  simp only [Submodule.mem_comap, Submodule.mem_map, LinearEquiv.coe_coe]
  rw [τ_tensor]
  constructor
  · rintro ⟨z, hz, hzy⟩
    exact ⟨z, hz, by rw [(transportEquiv B _).injective hzy]⟩
  · rintro ⟨z, hz, hzy⟩
    exact ⟨z, hz, by rw [(E.tensor B hB M).injective hzy]⟩

end FrameIso
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.DeligneDatum P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso.Twist"

namespace FrameIso

variable {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K]
variable {𝒪' : Type} [CommRing 𝒪'] {K' : Type} [Field K'] [Algebra 𝒪' K']

theorem isPullback_at_iff (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) {π : 𝒪} {π' : 𝒪'} (hπ : E.base π = π')
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (d d' : DeligneDatum (K := K) π B) (M : FullLattice 𝒪 K) :
    (E.deligne B hB hπ d').line (E.lattice M) =
        ((E.deligne B hB hπ d).line (FullLattice.act (E.gl g) (E.lattice M))).comap
          (actBaseChange B (E.gl g) (E.lattice M)).toLinearMap ↔
      d'.line M = (d.line (FullLattice.act g M)).comap (actBaseChange B g M).toLinearMap := by
  have hidx : (FullLattice.act (E.gl g) (E.lattice M)).1 = (E.lattice (FullLattice.act g M)).1 :=
    (congrArg Subtype.val (E.lattice_act g M)).symm

  have star : ((E.deligne B hB hπ d).line (FullLattice.act (E.gl g) (E.lattice M))).map (transportEquiv B hidx).toLinearMap =
      (d.line (FullLattice.act g M)).map (E.tensor B hB (FullLattice.act g M)).toLinearMap := by
    rw [← DeligneDatum.line_transport π' (E.deligne B hB hπ d) hidx, deligne_line]
  rw [deligne_line]
  constructor
  · intro h
    ext x
    have hx := congrArg (fun P : Submodule B _ => E.tensor B hB M x ∈ P) h
    simp only [Submodule.mem_map, Submodule.mem_comap, LinearEquiv.coe_coe] at hx
    rw [Submodule.mem_comap, LinearEquiv.coe_coe]

    have h1 : (∃ y, y ∈ d'.line M ∧ E.tensor B hB M y = E.tensor B hB M x) ↔ x ∈ d'.line M :=
      ⟨fun ⟨y, hy, hyx⟩ => by rwa [← (E.tensor B hB M).injective hyx], fun hx => ⟨x, hx, rfl⟩⟩
    rw [h1] at hx
    rw [hx]

    have h2 := congrArg (fun P : Submodule B _ => transportEquiv B hidx (actBaseChange B (E.gl g) (E.lattice M) (E.tensor B hB M x)) ∈ P) star
    simp only [Submodule.mem_map, LinearEquiv.coe_coe] at h2
    have sq := E.tensor_actBaseChange B hB g M x
    constructor
    · intro hmem
      obtain ⟨y, hy, hyx⟩ := h2.mp ⟨_, hmem, rfl⟩
      rw [← sq] at hyx
      rwa [← (E.tensor B hB _).injective hyx]
    · intro hmem
      obtain ⟨y, hy, hyx⟩ := h2.mpr ⟨_, hmem, sq⟩
      rwa [← (transportEquiv B hidx).injective hyx]
  · intro h
    ext y
    obtain ⟨x, rfl⟩ := (E.tensor B hB M).surjective y
    simp only [Submodule.mem_map, Submodule.mem_comap, LinearEquiv.coe_coe]
    have h2 := congrArg (fun P : Submodule B _ => transportEquiv B hidx (actBaseChange B (E.gl g) (E.lattice M) (E.tensor B hB M x)) ∈ P) star
    simp only [Submodule.mem_map, LinearEquiv.coe_coe] at h2
    have sq := E.tensor_actBaseChange B hB g M x
    constructor
    · rintro ⟨z, hz, hzx⟩
      rw [(E.tensor B hB M).injective hzx] at hz
      rw [h, Submodule.mem_comap, LinearEquiv.coe_coe] at hz
      obtain ⟨w, hw, hwx⟩ := h2.mpr ⟨_, hz, sq⟩
      rwa [← (transportEquiv B hidx).injective hwx]
    · intro hmem
      refine ⟨x, ?_, rfl⟩
      rw [h, Submodule.mem_comap, LinearEquiv.coe_coe]
      obtain ⟨w, hw, hwx⟩ := h2.mp ⟨_, hmem, rfl⟩
      rw [← sq] at hwx
      rwa [← (E.tensor B hB _).injective hwx]

theorem isPullback_deligne_iff (E : FrameIso 𝒪 K 𝒪' K') (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) {π : 𝒪} {π' : 𝒪'} (hπ : E.base π = π')
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (d d' : DeligneDatum (K := K) π B) :
    DeligneDatum.IsPullback (K := K') (π := π') B (E.gl g) (E.deligne B hB hπ d) (E.deligne B hB hπ d') ↔
      DeligneDatum.IsPullback (K := K) (π := π) B g d d' := by
  unfold DeligneDatum.IsPullback
  rw [← (E.lattice).forall_congr_right]
  exact forall_congr' fun M => E.isPullback_at_iff B hB hπ g d d' M

theorem tensor_rTensor (E : FrameIso 𝒪 K 𝒪' K') {B : Type} [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x))
    {B₁ : Type} [CommRing B₁] [Algebra 𝒪 B₁] [Algebra 𝒪' B₁]
    (hB₁ : ∀ x : 𝒪, algebraMap 𝒪 B₁ x = algebraMap 𝒪' B₁ (E.base x))
    (f : B →ₐ[𝒪] B₁) (f' : B →ₐ[𝒪'] B₁) (hff' : ∀ b, f b = f' b) (M : FullLattice 𝒪 K)
    (x : latticeBaseChange 𝒪 K B M) :
    E.tensor B₁ hB₁ M (LinearMap.rTensor (↥M.1) f.toLinearMap x) =
      LinearMap.rTensor (↥(E.lattice M).1) f'.toLinearMap (E.tensor B hB M x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [LinearMap.map_zero, LinearEquiv.map_zero]
  | add x y hx hy => simp only [LinearMap.map_add, LinearEquiv.map_add, hx, hy]
  | tmul b v =>
      rw [LinearMap.rTensor_tmul, tensor_tmul, tensor_tmul, LinearMap.rTensor_tmul]
      show f b ⊗ₜ[𝒪'] _ = f' b ⊗ₜ[𝒪'] _
      rw [hff']

theorem isBaseChange_deligne_iff (E : FrameIso 𝒪 K 𝒪' K') {π : 𝒪} {π' : 𝒪'} (hπ : E.base π = π')
    {B : Type} [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x))
    {B₁ : Type} [CommRing B₁] [Algebra 𝒪 B₁] [Algebra 𝒪' B₁]
    (hB₁ : ∀ x : 𝒪, algebraMap 𝒪 B₁ x = algebraMap 𝒪' B₁ (E.base x))
    (f : B →ₐ[𝒪] B₁) (f' : B →ₐ[𝒪'] B₁) (hff' : ∀ b, f b = f' b)
    (d : DeligneDatum (K := K) π B) (d₁ : DeligneDatum (K := K) π B₁) :
    DeligneDatum.IsBaseChange (K := K') (π := π') f' (E.deligne B hB hπ d) (E.deligne B₁ hB₁ hπ d₁) ↔
      DeligneDatum.IsBaseChange (K := K) (π := π) f d d₁ := by
  unfold DeligneDatum.IsBaseChange
  rw [← (E.lattice).forall_congr_right]
  refine forall_congr' fun M => ?_
  rw [deligne_line, deligne_line]
  have key : lineBaseChange f' (E.lattice M) ((d.line M).map (E.tensor B hB M).toLinearMap) =
      (lineBaseChange f M (d.line M)).map (E.tensor B₁ hB₁ M).toLinearMap := by
    unfold lineBaseChange
    rw [Submodule.map_span, Submodule.map_coe, ← Set.image_comp, ← Set.image_comp]
    congr 1
    apply Set.image_congr
    intro x _
    exact (E.tensor_rTensor hB hB₁ f f' hff' M x).symm
  rw [key]
  constructor
  · intro h
    exact Submodule.map_injective_of_injective (E.tensor B₁ hB₁ M).injective h
  · intro h; rw [h]

def omegaNr (E : FrameIso 𝒪 K 𝒪' K') {π : 𝒪} {π' : 𝒪'} (hπ : E.base π = π')
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Onr' : Type) [CommRing Onr'] [Algebra 𝒪' Onr']
    (eO : Onr ≃+* Onr') (heO : ∀ x : 𝒪, eO (algebraMap 𝒪 Onr x) = algebraMap 𝒪' Onr' (E.base x))
    (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x)) :
    OmegaNrObj (K := K) π Onr B ≃ OmegaNrObj (K := K') π' Onr' B :=
  Equiv.prodCongr (E.coeff Onr Onr' eO heO B hB) (E.deligne B hB hπ)

theorem isTwistedAct_omegaNr_iff (E : FrameIso 𝒪 K 𝒪' K') {π : 𝒪} {π' : 𝒪'} (hπ : E.base π = π')
    (Onr : Type) [CommRing Onr] [Algebra 𝒪 Onr] (Fr : Onr ≃ₐ[𝒪] Onr)
    (vdet : Matrix.GeneralLinearGroup (Fin 2) K →* Multiplicative ℤ)
    (Onr' : Type) [CommRing Onr'] [Algebra 𝒪' Onr'] (Fr' : Onr' ≃ₐ[𝒪'] Onr')
    (vdet' : Matrix.GeneralLinearGroup (Fin 2) K' →* Multiplicative ℤ)
    (eO : Onr ≃+* Onr') (heO : ∀ x : 𝒪, eO (algebraMap 𝒪 Onr x) = algebraMap 𝒪' Onr' (E.base x))
    (hFr : ∀ y, eO (Fr y) = Fr' (eO y)) (hv : ∀ g, vdet' (E.gl g) = vdet g)
    (B : Type) [CommRing B] [Algebra 𝒪 B] [Algebra 𝒪' B]
    (hB : ∀ x : 𝒪, algebraMap 𝒪 B x = algebraMap 𝒪' B (E.base x))
    (g : Matrix.GeneralLinearGroup (Fin 2) K) (x x' : OmegaNrObj (K := K) π Onr B) :
    OmegaNr.IsTwistedAct π' Onr' Fr' vdet' B (E.gl g)
        (E.omegaNr hπ Onr Onr' eO heO B hB x) (E.omegaNr hπ Onr Onr' eO heO B hB x') ↔
      OmegaNr.IsTwistedAct π Onr Fr vdet B g x x' := by
  unfold OmegaNr.IsTwistedAct
  refine and_congr ?_ ?_
  · show E.coeff Onr Onr' eO heO B hB x'.1 = frobTwist Onr' Fr' _ (E.coeff Onr Onr' eO heO B hB x.1) ↔ _
    rw [hv, ← E.coeff_frobTwist Onr Fr Onr' Fr' eO heO hFr B hB]
    exact (E.coeff Onr Onr' eO heO B hB).injective.eq_iff
  · show DeligneDatum.IsPullback (K := K') (π := π') B (E.gl g)⁻¹ (E.deligne B hB hπ x.2) (E.deligne B hB hπ x'.2) ↔ _
    rw [← map_inv]
    exact E.isPullback_deligne_iff B hB hπ g⁻¹ x.2 x'.2

end FrameIso
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.DeligneDatum P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso.Twist"

end CerednikDrinfeld.FormalOmega
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.DeligneDatum P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso.Twist P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega"
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.DeligneDatum P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso.Twist P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld"

open _root_.CerednikDrinfeld _root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld _root_.CerednikDrinfeld.FormalOmega _root_.P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega in
theorem solution
    {𝒪 : Type} [CommRing 𝒪] {K : Type} [Field K] [Algebra 𝒪 K] {π π₂ : 𝒪}
    (h : Ideal.span {π} = Ideal.span {π₂}) :
    ∃ Φ : ∀ (B : Type) [CommRing B] [Algebra 𝒪 B], DeligneDatum (K := K) π B ≃ DeligneDatum (K := K) π₂ B,
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (d : DeligneDatum (K := K) π B), (Φ B d).line = d.line) ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (g : Matrix.GeneralLinearGroup (Fin 2) K)
          (d d' : DeligneDatum (K := K) π B),
        DeligneDatum.IsPullback (K := K) (π := π₂) B g (Φ B d) (Φ B d') ↔
          DeligneDatum.IsPullback (K := K) (π := π) B g d d') ∧
      (∀ (B : Type) [CommRing B] [Algebra 𝒪 B] (B' : Type) [CommRing B'] [Algebra 𝒪 B'] (f : B →ₐ[𝒪] B')
          (d : DeligneDatum (K := K) π B) (d' : DeligneDatum (K := K) π B'),
        DeligneDatum.IsBaseChange (K := K) (π := π₂) f (Φ B d) (Φ B' d') ↔
          DeligneDatum.IsBaseChange (K := K) (π := π) f d d') := by
  exact ⟨fun B _ _ => DeligneDatum.congrOfSpanEq (K := K) h B, fun B _ _ d => rfl, fun B _ _ g d d' => Iff.rfl,
    fun B _ _ B' _ _ f d d' => Iff.rfl⟩

end
p2m_reactivate "P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.DeligneDatum P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega.FrameIso.Twist P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq.CerednikDrinfeld.FormalOmega"

end S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq
end P2MW
export P2MW.S_CerednikDrinfeld_FormalOmega_DeligneDatum_exists_equiv_of_span_singleton_eq (solution)
