-- Prove2me | solution 1 for Formalism.UG.P.levelvsplit_mem_range_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:38:50.134713+00:00
-- url     : https://prove2.me/submissions/272fb13c-c784-48d3-a88b-aba279b3c3dd

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stabstd
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Levelvsplit

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
variable {A R : Type} [CommRing A] [CommRing R] {n : Type} [Fintype n] [DecidableEq n]
namespace Formalism.UG.P
theorem _root_.solution (f : R →+* A) (hf : Function.Injective f) (g : GL n A) :
    g ∈ (bc (n := n) f).range ↔
      (∀ i j, (g : Matrix n n A) i j ∈ Set.range f) ∧
        ∀ i j, ((g⁻¹ : GL n A) : Matrix n n A) i j ∈ Set.range f := by
  constructor
  · intro hg
    obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hg
    refine ⟨fun i j => ⟨(u : Matrix n n R) i j, rfl⟩, fun i j => ⟨((u⁻¹ : GL n R) : Matrix n n R) i j, ?_⟩⟩
    rw [← map_inv (bc (n := n) f) u]
    rfl
  · rintro ⟨h1, h2⟩
    choose M hM using h1
    choose N hN using h2
    have hinj : Function.Injective (f.mapMatrix : Matrix n n R →+* Matrix n n A) := by
      intro X Y h
      ext i j
      have h' := congrArg (fun Z : Matrix n n A => Z i j) h
      exact hf h'
    have hMg : f.mapMatrix (Matrix.of M) = (g : Matrix n n A) := by
      ext i j
      exact hM i j
    have hNg : f.mapMatrix (Matrix.of N) = ((g⁻¹ : GL n A) : Matrix n n A) := by
      ext i j
      exact hN i j
    have e1 : Matrix.of M * Matrix.of N = 1 := hinj (by rw [map_mul, map_one, hMg, hNg, Units.mul_inv])
    have e2 : Matrix.of N * Matrix.of M = 1 := hinj (by rw [map_mul, map_one, hMg, hNg, Units.inv_mul])
    exact MonoidHom.mem_range.mpr ⟨⟨Matrix.of M, Matrix.of N, e1, e2⟩, Units.ext hMg⟩
end Formalism.UG.P
