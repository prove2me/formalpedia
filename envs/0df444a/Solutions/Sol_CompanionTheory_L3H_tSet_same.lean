-- Prove2me | solution 1 for CompanionTheory.L3H.tSet_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:29:33.450385+00:00
-- url     : https://prove2.me/submissions/125393d7-354e-44e0-a855-12779f1997c5

import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_ExistsDenFin
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeA
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_HeckeStdStatement
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_CompanionTheory_AutomorphicTheory_HeckeStandardModules_IntegralOfModule
import Theorems.Thm_CompanionTheory_L3H_tSet_iff
import Theorems.Thm_CompanionTheory_Split_emb_loc
import Theorems.Thm_CompanionTheory_Split_emb_triv
import Theorems.Thm_CompanionTheory_Split_loc_emb
import Theorems.Thm_CompanionTheory_Split_mem_Umax_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.UG Formalism.L2 CompanionTheory.Split CompanionTheory.HeckeA
noncomputable section
open CompanionTheory CompanionTheory.L3H
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
local notation3 "L⁺" => maximalRealSubfield L
variable {J : Subgroup (Formalism.AUTREP.GAf L n)} {χ : J →* ℂˣ} {B : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
namespace CompanionTheory.L3H
theorem _root_.solution (s s' : SplitPlace L) (hv : s'.v = s.v) {ϖ' : s'.v.adicCompletion L⁺} (h0 : ϖ' ≠ 0) (k : ℕ) :
    ∃ d : GL (Fin n) (s.v.adicCompletion L⁺), ∀ x, x ∈ Formalism.AUTREP.tSet L n s' ϖ' k ↔
      ∃ h ∈ DoubleCoset.doubleCoset d (KL s n : Set _) (KL s n), emb s n h = x := by
  obtain ⟨v, i⟩ := s'
  obtain rfl : v = s.v := hv
  let s' : SplitPlace L := ⟨s.v, i⟩
  have hK : ∀ a ∈ KL s' n, s.loc n (emb s' n a) ∈ KL s n := fun a ha =>
    (mem_Umax_iff s (emb_triv s' a)).1 ((mem_Umax_iff s' (emb_triv s' a)).2 (by rwa [loc_emb]))
  have hK' : ∀ a ∈ KL s n, s'.loc n (emb s n a) ∈ KL s' n := fun a ha =>
    (mem_Umax_iff s' (emb_triv s a)).1 ((mem_Umax_iff s (emb_triv s a)).2 (by rwa [loc_emb]))
  refine ⟨s.loc n (emb s' n (dg n s' h0 k)), fun x => ?_⟩
  rw [tSet_iff s' h0]
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hh
    refine ⟨_, DoubleCoset.mem_doubleCoset.2 ⟨_, hK a ha, _, hK b hb, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_mul, map_mul, emb_loc s (emb_triv s' a), emb_loc s (emb_triv s' _),
      emb_loc s (emb_triv s' b)]
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := DoubleCoset.mem_doubleCoset.1 hh
    refine ⟨s'.loc n (emb s n a) * dg n s' h0 k * s'.loc n (emb s n b),
      DoubleCoset.mem_doubleCoset.2 ⟨_, hK' a ha, _, hK' b hb, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_mul, map_mul, emb_loc s' (emb_triv s a), emb_loc s' (emb_triv s b),
      emb_loc s (emb_triv s' _)]
end CompanionTheory.L3H
