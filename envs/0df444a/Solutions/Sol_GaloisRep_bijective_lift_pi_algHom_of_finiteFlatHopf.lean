-- Prove2me | solution 1 for GaloisRep.bijective_lift_pi_algHom_of_finiteFlatHopf
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/c0ea34a2-b1bd-51ba-a1e9-f55231d02e29

import Mathlib
import Definitions.Def_GaloisRep_Flat
import Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
import Theorems.Thm_GaloisRep_natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRep_bijective_lift_pi_algHom_of_finiteFlatHopf

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section
open scoped TensorProduct Pointwise

namespace P2MMultEv

variable (q : ℕ) [Fact q.Prime]
variable (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
  [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
  [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H]

local notation "ℚ̄" => AlgebraicClosure ℚ

abbrev Pts : Type := WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄)

def evPt (φ : Pts q H) : ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H →ₐ[ℚ̄] ℚ̄ :=
  Algebra.TensorProduct.lift (AlgHom.id ℚ̄ ℚ̄) (WithConv.ofConv φ) (fun _ _ => Commute.all _ _)

theorem evPt_tmul (φ : Pts q H) (t : ℚ̄) (h : H) : evPt q H φ (t ⊗ₜ[GaloisRep.ratLocalizedAt q] h) = t * (WithConv.ofConv φ) h := by
  rw [evPt, Algebra.TensorProduct.lift_tmul]; rfl

def ev : ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H →ₐ[ℚ̄] (Pts q H → ℚ̄) := Pi.algHom ℚ̄ _ (fun φ => evPt q H φ)

theorem ev_apply (x : ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H) (φ : Pts q H) : ev q H x φ = evPt q H φ x := rfl

theorem ev_tmul (t : ℚ̄) (h : H) (φ : Pts q H) : ev q H (t ⊗ₜ[GaloisRep.ratLocalizedAt q] h) φ = t * (WithConv.ofConv φ) h := by
  rw [ev_apply, evPt_tmul]

scoped instance : IsDiscreteValuationRing (GaloisRep.ratLocalizedAt q) := GaloisRep.isDiscreteValuationRing_ratLocalizedAt q Fact.out

scoped instance instFreeH : Module.Free (GaloisRep.ratLocalizedAt q) H := Module.free_of_flat_of_isLocalRing

theorem finite_pts : Finite (Pts q H) := by
  apply Nat.finite_of_card_ne_zero
  rw [GaloisRep.natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf q H]
  haveI : Nontrivial H := by

    have h := Bialgebra.counit_one (R := GaloisRep.ratLocalizedAt q) (A := H)
    refine ⟨⟨1, 0, fun h10 => ?_⟩⟩
    have : (Coalgebra.counit (R := GaloisRep.ratLocalizedAt q) (A := H)) 1 = (Coalgebra.counit (R := GaloisRep.ratLocalizedAt q) (A := H)) 0 := by rw [h10]
    rw [h, map_zero] at this
    exact one_ne_zero this
  exact Module.finrank_pos.ne'

theorem linearIndependent_pts :
    LinearIndependent ℚ̄ (fun φ : Pts q H => ((WithConv.ofConv φ : H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄) : H → ℚ̄)) := by
  let χ : Pts q H → (H →* ℚ̄) := fun φ => (WithConv.ofConv φ : H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄).toMonoidHom
  have hχ : Function.Injective χ := by
    intro φ ψ h
    have : WithConv.ofConv φ = WithConv.ofConv ψ := AlgHom.ext fun x => by
      have := congrArg (fun f : H →* ℚ̄ => f x) h
      exact this
    calc φ = WithConv.toConv (WithConv.ofConv φ) := rfl
      _ = WithConv.toConv (WithConv.ofConv ψ) := by rw [this]
      _ = ψ := rfl
  exact (linearIndependent_monoidHom H ℚ̄).comp χ hχ

theorem ev_surjective : Function.Surjective (ev q H) := by
  classical
  haveI := finite_pts q H
  haveI : Fintype (Pts q H) := Fintype.ofFinite _

  suffices h : LinearMap.range (ev q H).toLinearMap = ⊤ from
    LinearMap.range_eq_top.mp h
  by_contra hne
  obtain ⟨f, hf0, hfr⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top (lt_top_iff_ne_top.mpr hne) inferInstance

  have hker : ∀ x, f (ev q H x) = 0 := by
    intro x
    have : f (ev q H x) ∈ Submodule.map f (LinearMap.range (ev q H).toLinearMap) :=
      Submodule.mem_map_of_mem ⟨x, rfl⟩
    rw [hfr] at this
    exact (Submodule.mem_bot ℚ̄).mp this

  set w : Pts q H → ℚ̄ := fun φ => f (Pi.single φ 1) with hw
  have hexp : ∀ c : Pts q H → ℚ̄, f c = ∑ φ, c φ * w φ := by
    intro c
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum]
    refine Finset.sum_congr rfl fun φ _ => ?_
    have : (Pi.single φ (c φ) : Pts q H → ℚ̄) = c φ • (Pi.single φ (1 : ℚ̄) : Pts q H → ℚ̄) := by
      ext ψ; simp [Pi.single_apply]
    rw [this, map_smul, smul_eq_mul]

  have hrel : ∑ φ, w φ • ((WithConv.ofConv φ : H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄) : H → ℚ̄) = 0 := by
    funext h
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    have := hker ((1 : ℚ̄) ⊗ₜ[GaloisRep.ratLocalizedAt q] h)
    rw [hexp] at this
    rw [← this]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [ev_tmul, one_mul, mul_comm]
  have hw0 : ∀ φ, w φ = 0 := Fintype.linearIndependent_iff.mp (linearIndependent_pts q H) w hrel
  apply hf0
  apply LinearMap.ext
  intro c
  rw [hexp c, LinearMap.zero_apply]
  exact Finset.sum_eq_zero fun φ _ => by rw [hw0 φ, mul_zero]

theorem finrank_baseChange_eq :
    Module.finrank ℚ̄ (ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H) = Module.finrank (GaloisRep.ratLocalizedAt q) H :=
  Module.finrank_baseChange

theorem ev_bijective : Function.Bijective (ev q H) := by
  classical
  haveI := finite_pts q H
  haveI : Fintype (Pts q H) := Fintype.ofFinite _
  refine ⟨?_, ev_surjective q H⟩

  have hdim : Module.finrank ℚ̄ (ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H) = Module.finrank ℚ̄ (Pts q H → ℚ̄) := by
    rw [finrank_baseChange_eq, Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card,
      GaloisRep.natCard_withConv_algHom_eq_finrank_of_finiteFlatHopf q H]
  have := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim (f := (ev q H).toLinearMap)).mpr
    (ev_surjective q H)
  exact this

def evEquiv : ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H ≃ₐ[ℚ̄] (Pts q H → ℚ̄) :=
  AlgEquiv.ofBijective (ev q H) (ev_bijective q H)

theorem evEquiv_apply (x : ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H) : evEquiv q H x = ev q H x := rfl

theorem evEquiv_tmul (t : ℚ̄) (h : H) (φ : Pts q H) :
    evEquiv q H (t ⊗ₜ[GaloisRep.ratLocalizedAt q] h) φ = t * (WithConv.ofConv φ) h := ev_tmul q H t h φ

def resR (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) : ℚ̄ →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄ := (σ : ℚ̄ →ₐ[ℚ] ℚ̄).restrictScalars _

@[scoped simp] theorem resR_apply (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (t : ℚ̄) : resR q σ t = σ t := rfl

def galT (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) : ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H →ₐ[GaloisRep.ratLocalizedAt q] ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H :=
  Algebra.TensorProduct.map (resR q σ) (AlgHom.id _ H)

theorem galT_tmul (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (t : ℚ̄) (h : H) :
    galT q H σ (t ⊗ₜ[GaloisRep.ratLocalizedAt q] h) = σ t ⊗ₜ[GaloisRep.ratLocalizedAt q] h := by
  first
    | rfl
    | (show (Algebra.TensorProduct.map (resR q σ) (AlgHom.id _ H)) (t ⊗ₜ[GaloisRep.ratLocalizedAt q] h) = _
       erw [Algebra.TensorProduct.map_tmul]; rfl)

theorem gal_algebraMap (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (r : GaloisRep.ratLocalizedAt q) :
    σ (algebraMap (GaloisRep.ratLocalizedAt q) ℚ̄ r) = algebraMap (GaloisRep.ratLocalizedAt q) ℚ̄ r := by
  rw [IsScalarTower.algebraMap_apply (GaloisRep.ratLocalizedAt q) ℚ ℚ̄ r]
  exact σ.commutes _

def galPt (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (φ : Pts q H) : Pts q H := WithConv.toConv ((resR q σ).comp (WithConv.ofConv φ))

@[scoped simp] theorem ofConv_galPt_apply (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (φ : Pts q H) (h : H) :
    (WithConv.ofConv (galPt q H σ φ)) h = σ ((WithConv.ofConv φ) h) := rfl

theorem galPt_mul (σ τ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (φ : Pts q H) : galPt q H (σ * τ) φ = galPt q H σ (galPt q H τ φ) := rfl

theorem galPt_one (φ : Pts q H) : galPt q H 1 φ = φ := rfl

theorem ev_galT (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H) (φ : Pts q H) :
    ev q H (galT q H σ x) φ = σ (ev q H x (galPt q H σ⁻¹ φ)) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t h =>
      rw [galT_tmul, ev_tmul, ev_tmul, map_mul, ofConv_galPt_apply, ← AlgEquiv.mul_apply, mul_inv_cancel,
        AlgEquiv.one_apply]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

theorem ev_galT' (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (x : ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H) (φ : Pts q H) :
    ev q H (galT q H σ x) (galPt q H σ φ) = σ (ev q H x φ) := by
  rw [ev_galT, ← galPt_mul, inv_mul_cancel, galPt_one]

theorem basis_repr_galT {ι : Type} (b : Module.Basis ι (GaloisRep.ratLocalizedAt q) H) (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄)
    (x : ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H) (i : ι) :
    (Algebra.TensorProduct.basis ℚ̄ b).repr (galT q H σ x) i = σ ((Algebra.TensorProduct.basis ℚ̄ b).repr x i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero, Finsupp.zero_apply]
  | tmul t h =>
      rw [galT_tmul, Algebra.TensorProduct.basis_repr_tmul, Algebra.TensorProduct.basis_repr_tmul,
        Finsupp.smul_apply, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul, smul_eq_mul, map_mul,
        gal_algebraMap]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

theorem galT_eq_self_iff_repr_mem {ι : Type} (b : Module.Basis ι (GaloisRep.ratLocalizedAt q) H)
    (D : Subgroup (ℚ̄ ≃ₐ[ℚ] ℚ̄)) (x : ℚ̄ ⊗[GaloisRep.ratLocalizedAt q] H) :
    (∀ σ ∈ D, galT q H σ x = x) ↔
      ∀ i, (Algebra.TensorProduct.basis ℚ̄ b).repr x i ∈ IntermediateField.fixedField D := by
  constructor
  · intro h i
    rw [IntermediateField.mem_fixedField_iff]
    intro σ hσ
    have := congrArg (fun y => (Algebra.TensorProduct.basis ℚ̄ b).repr y i) (h σ hσ)
    simp only [basis_repr_galT] at this
    exact this
  · intro h σ hσ
    apply (Algebra.TensorProduct.basis ℚ̄ b).repr.injective
    ext i
    rw [basis_repr_galT]
    exact (IntermediateField.mem_fixedField_iff D _).mp (h i) σ hσ

scoped instance instMulActionPts : MulAction (ℚ̄ ≃ₐ[ℚ] ℚ̄) (Pts q H) where
  smul := galPt q H
  one_smul := galPt_one q H
  mul_smul := galPt_mul q H

theorem smul_pts_def (σ : ℚ̄ ≃ₐ[ℚ] ℚ̄) (φ : Pts q H) : σ • φ = galPt q H σ φ := rfl

theorem isAlgebraic_qbar : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := by
  convert AlgebraicClosure.isAlgebraic ℚ
  rfl
  rfl

theorem isAlgClosure_qbar : IsAlgClosure ℚ (AlgebraicClosure ℚ) :=
  (isAlgClosure_iff ℚ (AlgebraicClosure ℚ)).mpr ⟨inferInstance, isAlgebraic_qbar⟩

scoped instance normal_qbar : Normal ℚ ℚ̄ := @IsAlgClosure.normal ℚ ℚ̄ _ _ _ (isAlgClosure_qbar)

theorem exists_level : ∃ E : IntermediateField ℚ ℚ̄, FiniteDimensional ℚ E ∧ Normal ℚ E ∧
    ∀ σ : ℚ̄ ≃ₐ[ℚ] ℚ̄, (∀ e : ℚ̄, e ∈ E → σ e = e) → ∀ φ : Pts q H, σ • φ = φ := by
  classical
  haveI := finite_pts q H
  haveI : Fintype (Pts q H) := Fintype.ofFinite _
  obtain ⟨s, hs⟩ : (⊤ : Submodule (GaloisRep.ratLocalizedAt q) H).FG := Module.finite_def.mp inferInstance

  let V : Finset ℚ̄ := (Finset.univ ×ˢ s).image fun p : Pts q H × H => (WithConv.ofConv p.1) p.2
  have hVint : ∀ x ∈ (V : Set ℚ̄), IsIntegral ℚ x := fun x _ => (isAlgebraic_qbar.isAlgebraic x).isIntegral
  haveI : Finite (↑(V : Set ℚ̄)) := Finite.of_fintype _
  let K : IntermediateField ℚ ℚ̄ := IntermediateField.adjoin ℚ (V : Set ℚ̄)
  haveI hKfd : FiniteDimensional ℚ K := IntermediateField.finiteDimensional_adjoin hVint
  let E : IntermediateField ℚ ℚ̄ := IntermediateField.normalClosure ℚ K ℚ̄
  refine ⟨E, normalClosure.is_finiteDimensional ℚ K ℚ̄, normalClosure.normal ℚ K ℚ̄, ?_⟩
  intro σ hσ φ
  have hKE : K ≤ E := IntermediateField.le_normalClosure K

  have hfix : ∀ h ∈ s, σ ((WithConv.ofConv φ) h) = (WithConv.ofConv φ) h := by
    intro h hh
    apply hσ
    apply hKE
    apply IntermediateField.subset_adjoin
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(φ, h), Finset.mem_product.mpr ⟨Finset.mem_univ _, hh⟩, rfl⟩)

  have hall : ∀ h : H, σ ((WithConv.ofConv φ) h) = (WithConv.ofConv φ) h := by
    intro h
    have hmem : h ∈ Submodule.span (GaloisRep.ratLocalizedAt q) (s : Set H) := by rw [hs]; trivial
    induction hmem using Submodule.span_induction with
    | mem y hy => exact hfix y hy
    | zero => simp
    | add y z _ _ hy hz => rw [map_add, map_add, hy, hz]
    | smul r y _ hy =>
        show σ ((WithConv.ofConv φ) (r • y)) = (WithConv.ofConv φ) (r • y)
        rw [Algebra.smul_def, map_mul, AlgHom.commutes, map_mul, gal_algebraMap, hy]

  rw [smul_pts_def]
  show WithConv.toConv ((resR q σ).comp (WithConv.ofConv φ)) = φ
  have : (resR q σ).comp (WithConv.ofConv φ) = WithConv.ofConv φ := AlgHom.ext fun h => hall h
  rw [this]

end P2MMultEv
p2m_reactivate "P2MW.S_GaloisRep_bijective_lift_pi_algHom_of_finiteFlatHopf.P2MMultEv"
end
p2m_reactivate "P2MW.S_GaloisRep_bijective_lift_pi_algHom_of_finiteFlatHopf.P2MMultEv"

open scoped TensorProduct

set_option maxHeartbeats 3200000 in

theorem solution
    (q : ℕ) [Fact q.Prime]
    (H : Type) [CommRing H] [HopfAlgebra (GaloisRep.ratLocalizedAt q) H]
    [Module.Finite (GaloisRep.ratLocalizedAt q) H] [Module.Flat (GaloisRep.ratLocalizedAt q) H]
    [Coalgebra.IsCocomm (GaloisRep.ratLocalizedAt q) H] :
    Function.Bijective
      (Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
        (Pi.algHom (GaloisRep.ratLocalizedAt q) _
          fun ν : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) => (WithConv.ofConv ν : H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure ℚ ⊗[GaloisRep.ratLocalizedAt q] H →ₐ[AlgebraicClosure ℚ] (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)) := by

  have h : ⇑(Algebra.TensorProduct.lift
        (Algebra.ofId (AlgebraicClosure ℚ) (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) → AlgebraicClosure ℚ))
        (Pi.algHom (GaloisRep.ratLocalizedAt q) _
          fun ν : WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) => (WithConv.ofConv ν : H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ))
        (fun _ _ => Commute.all _ _) :
        AlgebraicClosure ℚ ⊗[GaloisRep.ratLocalizedAt q] H →ₐ[AlgebraicClosure ℚ] (WithConv (H →ₐ[GaloisRep.ratLocalizedAt q] AlgebraicClosure ℚ) → AlgebraicClosure ℚ)) = ⇑(P2MMultEv.ev q H) := by
    funext x; funext φ
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]
    | tmul t hh =>
        rw [P2MMultEv.ev_tmul, Algebra.TensorProduct.lift_tmul, Pi.mul_apply, Pi.algHom_apply, Algebra.ofId_apply,
          Pi.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  rw [h]
  exact P2MMultEv.ev_bijective q H

end S_GaloisRep_bijective_lift_pi_algHom_of_finiteFlatHopf
end P2MW
export P2MW.S_GaloisRep_bijective_lift_pi_algHom_of_finiteFlatHopf (solution)
