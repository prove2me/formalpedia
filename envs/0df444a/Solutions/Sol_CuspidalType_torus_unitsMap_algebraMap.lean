-- Prove2me | solution 1 for CuspidalType.torus_unitsMap_algebraMap
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/eca178d0-ce56-5d44-9d33-429bef469d4e

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CuspidalType_torus_unitsMap_algebraMap

set_option autoImplicit false

p2m_open "Polynomial CuspidalType P2MW.S_CuspidalType_torus_unitsMap_algebraMap.CuspidalType"

namespace CuspidalType
p2m_export "CuspidalType" "GL2 scalarElem quadBasis torus"
namespace TorusAPI
p2m_open "CuspidalType"

variable (q : ℕ) [Fact q.Prime]

theorem coe_torus (α : (GaloisField q 2)ˣ) :
    ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) =
      LinearMap.toMatrix (quadBasis q) (quadBasis q) (Algebra.lmul (ZMod q) (GaloisField q 2) (α : GaloisField q 2)) :=
  rfl

theorem coe_scalarElem (c : (ZMod q)ˣ) :
    ((scalarElem q c : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)) = Matrix.scalar (Fin 2) (c : ZMod q) :=
  rfl

theorem toMatrix_lmul_algebraMap (c : ZMod q) :
    LinearMap.toMatrix (quadBasis q) (quadBasis q)
        (Algebra.lmul (ZMod q) (GaloisField q 2) (algebraMap (ZMod q) (GaloisField q 2) c)) =
      Matrix.scalar (Fin 2) c := by
  ext i j
  rw [LinearMap.toMatrix_apply]
  change (quadBasis q).repr (algebraMap (ZMod q) (GaloisField q 2) c * (quadBasis q) j) i = _
  rw [← Algebra.smul_def, map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_apply,
    Matrix.scalar_apply, Matrix.diagonal_apply]
  by_cases h : i = j
  · subst h; simp
  · rw [if_neg (Ne.symm h), if_neg h, smul_zero]

theorem torus_unitsMap_algebraMap (c : (ZMod q)ˣ) :
    torus q (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = scalarElem q c := by
  apply Units.ext
  rw [coe_torus, coe_scalarElem]
  exact toMatrix_lmul_algebraMap q (c : ZMod q)

theorem torus_injective : Function.Injective (torus q) := by
  intro α β h
  apply Units.ext
  have h1 := congrArg (fun g : GL2 q => (g : Matrix (Fin 2) (Fin 2) (ZMod q))) h
  simp only [coe_torus] at h1
  exact Algebra.lmul_injective ((LinearMap.toMatrix (quadBasis q) (quadBasis q)).injective h1)

theorem charpoly_torus (α : (GaloisField q 2)ˣ) :
    ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly =
      (Algebra.lmul (ZMod q) (GaloisField q 2) (α : GaloisField q 2)).charpoly := by
  rw [coe_torus, LinearMap.charpoly_toMatrix]

theorem finrank_two : Module.finrank (ZMod q) (GaloisField q 2) = 2 := GaloisField.finrank q two_ne_zero

variable {q}

theorem natDegree_minpoly_eq_two {a : GaloisField q 2}
    (ha : a ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))) :
    (minpoly (ZMod q) a).natDegree = 2 ∧ IntermediateField.adjoin (ZMod q) ({a} : Set (GaloisField q 2)) = ⊤ := by
  have hint : IsIntegral (ZMod q) a := Algebra.IsIntegral.isIntegral a
  have hdvd : (minpoly (ZMod q) a).natDegree ∣ 2 := by
    rw [← IntermediateField.adjoin.finrank hint]
    have h := Module.finrank_mul_finrank (ZMod q) ↥(IntermediateField.adjoin (ZMod q) ({a} : Set (GaloisField q 2)))
      (GaloisField q 2)
    rw [finrank_two q] at h
    exact Dvd.intro _ h
  have hne1 : (minpoly (ZMod q) a).natDegree ≠ 1 := by
    intro h1
    apply ha
    have := minpoly.natDegree_eq_one_iff.mp h1
    exact this
  have h2 : (minpoly (ZMod q) a).natDegree = 2 := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  refine ⟨h2, ?_⟩
  rw [Field.primitive_element_iff_minpoly_natDegree_eq, h2, finrank_two q]

theorem charpoly_lmul_eq_minpoly {a : GaloisField q 2}
    (ha : a ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))) :
    (Algebra.lmul (ZMod q) (GaloisField q 2) a).charpoly = minpoly (ZMod q) a := by
  classical
  obtain ⟨h2, htop⟩ := natDegree_minpoly_eq_two ha
  have hint : IsIntegral (ZMod q) a := Algebra.IsIntegral.isIntegral a

  let pb₀ := IntermediateField.adjoin.powerBasis hint
  let e : ↥(IntermediateField.adjoin (ZMod q) ({a} : Set (GaloisField q 2))) ≃ₐ[ZMod q] GaloisField q 2 :=
    (IntermediateField.equivOfEq htop).trans IntermediateField.topEquiv
  let pb : PowerBasis (ZMod q) (GaloisField q 2) := pb₀.map e
  have hgen : pb.gen = a := by
    show e pb₀.gen = a
    rw [IntermediateField.adjoin.powerBasis_gen]
    rfl
  rw [← LinearMap.charpoly_toMatrix _ pb.basis, ← hgen, ← Algebra.leftMulMatrix_apply, charpoly_leftMulMatrix]

theorem not_isRoot_charpoly_torus {α : (GaloisField q 2)ˣ}
    (hα : (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))) (x : ZMod q) :
    ¬ ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly.IsRoot x := by
  rw [charpoly_torus, charpoly_lmul_eq_minpoly hα]
  intro hx
  obtain ⟨h2, -⟩ := natDegree_minpoly_eq_two hα
  have hirr : Irreducible (minpoly (ZMod q) (α : GaloisField q 2)) :=
    minpoly.irreducible (Algebra.IsIntegral.isIntegral _)
  have hdvd : (X - C x) ∣ minpoly (ZMod q) (α : GaloisField q 2) := Polynomial.dvd_iff_isRoot.mpr hx
  obtain ⟨r, hr⟩ := hdvd
  rcases hirr.isUnit_or_isUnit hr with hu | hu
  · exact Polynomial.not_isUnit_X_sub_C x hu
  · have hdeg := congrArg Polynomial.natDegree hr
    rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero x) hu.ne_zero, Polynomial.natDegree_X_sub_C,
      Polynomial.natDegree_eq_zero_of_isUnit hu, h2] at hdeg
    omega

theorem aeval_charpoly_torus' (α : (GaloisField q 2)ˣ) :
    aeval (α : GaloisField q 2) ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly = 0 := by
  rw [charpoly_torus]
  have h := LinearMap.aeval_self_charpoly (Algebra.lmul (ZMod q) (GaloisField q 2) (α : GaloisField q 2))
  rw [Polynomial.aeval_algHom_apply] at h
  exact Algebra.lmul_injective (h.trans (map_zero _).symm)

theorem charpoly_torus_eq_minpoly' {α : (GaloisField q 2)ˣ}
    (hα : (α : GaloisField q 2) ∉ Set.range (algebraMap (ZMod q) (GaloisField q 2))) :
    ((torus q α : GL2 q) : Matrix (Fin 2) (Fin 2) (ZMod q)).charpoly = minpoly (ZMod q) (α : GaloisField q 2) ∧
    Irreducible (minpoly (ZMod q) (α : GaloisField q 2)) ∧ (minpoly (ZMod q) (α : GaloisField q 2)).natDegree = 2 :=
  ⟨by rw [charpoly_torus, charpoly_lmul_eq_minpoly hα], minpoly.irreducible (Algebra.IsIntegral.isIntegral _),
    (natDegree_minpoly_eq_two hα).1⟩

end CuspidalType.TorusAPI

theorem solution (q : ℕ) [Fact q.Prime] (c : (ZMod q)ˣ) :
    torus q (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = scalarElem q c :=
  CuspidalType.TorusAPI.torus_unitsMap_algebraMap q c

end S_CuspidalType_torus_unitsMap_algebraMap
end P2MW
export P2MW.S_CuspidalType_torus_unitsMap_algebraMap (solution)
