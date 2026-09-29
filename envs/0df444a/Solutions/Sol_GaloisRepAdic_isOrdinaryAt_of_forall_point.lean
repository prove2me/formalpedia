-- Prove2me | solution 1 for GaloisRepAdic.isOrdinaryAt_of_forall_point
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.331093+00:00
-- url     : https://prove2.me/submissions/4c7e98d7-b1dd-5595-92ed-e2f9fad90275

import Definitions.Def_GaloisRep_LocalConditions
import Theorems.Thm_GaloisRepAdic_isOrdinaryAt_of_jointly_injective
import Theorems.Thm_GaloisRepAdic_detIsCyclotomic_baseChangeAlong
import Theorems.Thm_GaloisRepAdic_isOrdinaryAt_of_isEquiv
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_GaloisRepAdic_isOrdinaryAt_of_forall_point

open scoped TensorProduct

namespace GaloisRepAdic
p2m_export "GaloisRepAdic" "DetIsCyclotomic IsOrdinaryAt baseChangeAlong IsEquiv ρ mk V isOrdinaryAt_of_jointly_injective detIsCyclotomic_baseChangeAlong isOrdinaryAt_of_isEquiv"
p2m_open "GaloisRepAdic"

theorem isEquiv_baseChangeAlong_baseChangeAlong
    {A B C : Type} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [CommRing C] [IsLocalRing C]
    (φ : A →+* B) (hφ : IsLocalHom φ) (ψ : B →+* C) (hψ : IsLocalHom ψ)
    (χ : A →+* C) (hχ : IsLocalHom χ) (hcomp : ψ.comp φ = χ) (ρ : GaloisRepAdic A) :
    ((ρ.baseChangeAlong φ hφ).baseChangeAlong ψ hψ).IsEquiv (ρ.baseChangeAlong χ hχ) := by
  subst hcomp
  letI : Algebra A B := φ.toAlgebra
  letI : Algebra B C := ψ.toAlgebra
  letI : Algebra A C := (ψ.comp φ).toAlgebra
  haveI : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact ⟨{ toLinearEquiv := TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
           map_apply := fun σ x => by
             show TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V
                 (((ρ.ρ σ).baseChange B).baseChange C x) =
               ((ρ.ρ σ).baseChange C)
                 (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C ρ.V x)
             rw [LinearMap.baseChange_baseChange]
             exact (TensorProduct.AlgebraTensorModule.cancelBaseChange A B C C
               ρ.V).apply_symm_apply _ }⟩

theorem _root_.P2MW.S_GaloisRepAdic_isOrdinaryAt_of_forall_point.solution
    {P : Type} [CommRing P] [IsLocalRing P]
    {n : ℕ} {A : Fin n → Type} [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
    (χ : ∀ i, P →+* A i) (hχ : ∀ i, IsLocalHom (χ i))
    (hinj : ∀ x : P, (∀ i, χ i x = 0) → x = 0)
    (ρ : GaloisRepAdic P) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hdet : ρ.DetIsCyclotomic p)
    (hord : ∀ i, (ρ.baseChangeAlong (χ i) (hχ i)).IsOrdinaryAt p) :
    ρ.IsOrdinaryAt p := by
  revert P A
  induction n with
  | zero =>
    intro P _ _ A _ _ χ hχ hinj ρ hdet hord
    exact absurd (hinj 1 fun i => i.elim0) one_ne_zero
  | succ n ih =>
    intro P instCP instLP A instCA instLA χ hχ hinj ρ hdet hord
    rcases Nat.eq_zero_or_pos n with rfl | hn
    ·
      exact isOrdinaryAt_of_jointly_injective (χ 0) (hχ 0) (χ 0) (hχ 0)
        (fun x h0 _ => hinj x fun i => Fin.cases h0 (fun j => j.elim0) i)
        ρ hp hp2 (detIsCyclotomic_baseChangeAlong (χ 0) (hχ 0) ρ hdet) (hord 0) (hord 0)
    ·
      set J : Ideal P := ⨅ i : Fin n, RingHom.ker (χ i.succ) with hJdef
      have hmemJ : ∀ x : P, x ∈ J ↔ ∀ i : Fin n, χ i.succ x = 0 := fun x => by
        rw [hJdef]
        simp [RingHom.mem_ker]
      have hJne : J ≠ ⊤ := by
        intro htop
        have h1 : (1 : P) ∈ J := by rw [htop]; exact Submodule.mem_top
        have h2 : χ (Fin.succ ⟨0, hn⟩) 1 = 0 := (hmemJ 1).mp h1 ⟨0, hn⟩
        rw [map_one] at h2
        exact one_ne_zero h2
      haveI : Nontrivial (P ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJne
      haveI : IsLocalRing (P ⧸ J) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective
      haveI hmk : IsLocalHom (Ideal.Quotient.mk J) :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      have hle : ∀ i : Fin n, ∀ a : P, a ∈ J → χ i.succ a = 0 := fun i a ha =>
        (hmemJ a).mp ha i
      let χ' : ∀ i : Fin n, P ⧸ J →+* A i.succ := fun i =>
        Ideal.Quotient.lift J (χ i.succ) (hle i)
      have hχ'mk : ∀ (i : Fin n) (x : P), χ' i (Ideal.Quotient.mk J x) = χ i.succ x :=
        fun i x => Ideal.Quotient.lift_mk J (χ i.succ) (hle i)
      have hχ' : ∀ i, IsLocalHom (χ' i) := fun i =>
        ⟨fun y hy => by
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
          rw [hχ'mk i x] at hy
          exact ((hχ i.succ).map_nonunit x hy).map (Ideal.Quotient.mk J)⟩
      have hinj' : ∀ y : P ⧸ J, (∀ i, χ' i y = 0) → y = 0 := fun y hy => by
        obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [Ideal.Quotient.eq_zero_iff_mem]
        exact (hmemJ x).mpr fun i => by rw [← hχ'mk i x]; exact hy i
      have hcomp : ∀ i : Fin n, (χ' i).comp (Ideal.Quotient.mk J) = χ i.succ :=
        fun i => RingHom.ext fun x => hχ'mk i x
      have hordQ : (ρ.baseChangeAlong (Ideal.Quotient.mk J) hmk).IsOrdinaryAt p := by
        refine ih χ' hχ' hinj' (ρ.baseChangeAlong (Ideal.Quotient.mk J) hmk)
          (detIsCyclotomic_baseChangeAlong _ hmk ρ hdet) (fun i => ?_)
        obtain ⟨e⟩ := isEquiv_baseChangeAlong_baseChangeAlong (Ideal.Quotient.mk J) hmk
          (χ' i) (hχ' i) (χ i.succ) (hχ i.succ) (hcomp i) ρ
        exact isOrdinaryAt_of_isEquiv ⟨e.symm⟩ (hord i.succ)
      exact isOrdinaryAt_of_jointly_injective (χ 0) (hχ 0) (Ideal.Quotient.mk J) hmk
        (fun x h0 hQ => hinj x fun i => Fin.cases h0
          (fun j => (hmemJ x).mp (Ideal.Quotient.eq_zero_iff_mem.mp hQ) j) i)
        ρ hp hp2 (detIsCyclotomic_baseChangeAlong (χ 0) (hχ 0) ρ hdet) (hord 0) hordQ

end GaloisRepAdic

end S_GaloisRepAdic_isOrdinaryAt_of_forall_point
end P2MW
export P2MW.S_GaloisRepAdic_isOrdinaryAt_of_forall_point (solution)
