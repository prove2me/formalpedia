-- Prove2me | solution 1 for Formalism.UG.P.levelaf_conj_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T11:38:53.22645+00:00
-- url     : https://prove2.me/submissions/cb526f85-8fe6-4d7b-9e56-fe580559e981

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped WithZero TensorProduct
variable {L : Type} [CommRing L] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (O : Subring L) (g : GL n L) (c : O)
    (hg : (c : L) • (g : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (hg' : (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range)
    (h : GL n O) (hh : redGL (n := n) (Ideal.span {c * c}) h = 1) :
    ((g⁻¹ * bc (n := n) O.subtype h * g : GL n L) : Matrix n n L) ∈
      (RingHom.mapMatrix (m := n) O.subtype).range := by
  have hm : RingHom.mapMatrix (m := n) (Ideal.Quotient.mk (Ideal.span {c * c})) (h : Matrix n n O) =
      RingHom.mapMatrix (m := n) (Ideal.Quotient.mk (Ideal.span {c * c})) 1 := by
    rw [map_one]; exact congrArg Units.val hh
  have hent : ∀ a b, (h : Matrix n n O) a b - (1 : Matrix n n O) a b ∈ Ideal.span {c * c} := by
    intro a b
    rw [← Ideal.Quotient.eq]
    simpa only [RingHom.mapMatrix_apply, Matrix.map_apply] using congrFun (congrFun hm a) b
  choose e he using fun a b => Ideal.mem_span_singleton'.1 (hent a b)
  let E : Matrix n n O := Matrix.of e
  have hL : ∀ a b, (((h : Matrix n n O) a b : O) : L) =
      (1 : Matrix n n L) a b + (c : L) * (c : L) * ((e a b : O) : L) := by
    intro a b
    have h1 := he a b
    rw [Matrix.one_apply] at h1 ⊢
    split_ifs at h1 ⊢ with hab
    · have := congrArg Subtype.val h1
      push_cast at this
      linear_combination -this
    · have := congrArg Subtype.val h1
      push_cast at this
      linear_combination -this
  have hkey : ((bc (n := n) O.subtype h : GL n L) : Matrix n n L) =
      1 + ((c : L) * (c : L)) • RingHom.mapMatrix (m := n) O.subtype E := by
    ext a b
    simp only [bc, Units.coe_map, MonoidHom.coe_coe, RingHom.toMonoidHom_eq_coe,
      RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
      E, Matrix.of_apply, Subring.coe_subtype]
    exact hL a b
  have hcalc : ((g⁻¹ * bc (n := n) O.subtype h * g : GL n L) : Matrix n n L) =
      1 + ((c : L) • ((g⁻¹ : GL n L) : Matrix n n L)) * RingHom.mapMatrix (m := n) O.subtype E *
        ((c : L) • (g : Matrix n n L)) := by
    rw [Units.val_mul, Units.val_mul, hkey, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      ← Units.val_mul, inv_mul_cancel, Units.val_one]
    congr 1
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.mul_assoc]
  rw [hcalc]
  exact add_mem (one_mem _) (mul_mem (mul_mem hg' ⟨E, rfl⟩) hg)
end Formalism.UG.P
