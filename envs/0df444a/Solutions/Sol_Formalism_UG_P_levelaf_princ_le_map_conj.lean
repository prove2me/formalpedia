-- Prove2me | solution 1 for Formalism.UG.P.levelaf_princ_le_map_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:51:23.434338+00:00
-- url     : https://prove2.me/submissions/035dacf1-5992-4d9a-b8d1-4793a6b9ed99

import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelaf
import Theorems.Thm_Formalism_UG_P_levelaf_mem_range_of_integral
import Theorems.Thm_Formalism_UG_P_levelaf_conj_integral

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
    (hg' : (c : L) • ((g⁻¹ : GL n L) : Matrix n n L) ∈ (RingHom.mapMatrix (m := n) O.subtype).range) :
    princ (n := n) O.subtype (Ideal.span {c * c}) ≤
      (bc (n := n) O.subtype).range.map (MulAut.conj g).toMonoidHom := by
  intro k hk
  simp only [princ, congPre] at hk
  obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hk
  have hh' : redGL (n := n) (Ideal.span {c * c}) h = 1 := by
    simpa only [Subgroup.mem_comap, Subgroup.mem_bot] using hh
  have hh'' : redGL (n := n) (Ideal.span {c * c}) h⁻¹ = 1 := by rw [map_inv, hh', inv_one]
  refine Subgroup.mem_map.2 ⟨g⁻¹ * bc (n := n) O.subtype h * g, ?_, ?_⟩
  · apply levelaf_mem_range_of_integral
    · exact levelaf_conj_integral O g c hg hg' h hh'
    · have : (g⁻¹ * bc (n := n) O.subtype h * g)⁻¹ = g⁻¹ * bc (n := n) O.subtype h⁻¹ * g := by
        rw [map_inv]; group
      rw [this]
      exact levelaf_conj_integral O g c hg hg' h⁻¹ hh''
  · simp [MulAut.conj_apply, mul_assoc]
end Formalism.UG.P
