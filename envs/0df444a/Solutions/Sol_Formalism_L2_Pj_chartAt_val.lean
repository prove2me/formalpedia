-- Prove2me | solution 1 for Formalism.L2.Pj.chartAt_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:57:32.938223+00:00
-- url     : https://prove2.me/submissions/5d9696a9-d6a0-4c62-8c9e-088c332666e3

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_AlgebraMapCAt
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_ChartWD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj
variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable {pts mapR borR}
namespace Formalism.L2.Pj
theorem _root_.solution {f : Rules pts} (hf : IsNatural pts mapR f) {S : Type} [CommRing S] [Algebra K S] {w : pts S}
    {m : Ideal S} [m.IsPrime] {A : TRing K} {u : pts A.R} {c : A.R →ₐ[K] Localization.AtPrime m}
    (hc : FrChartAt pts mapR w m A u c) {p : TRing K} {φ : p.R →ₐ[K] S} {y : pts p.R} (hy : mapR φ y w) :
    locM K m (φ (f p y)) = c (f A u) := by
  obtain ⟨p', lam, a, μ, y', h1, h2, h3, h4⟩ := hc p φ y hy
  have e1 : f p' y' = lam (f p y) := hf p p' lam y y' h1
  have e2 : f p' y' = a (f A u) := hf A p' a u y' h2
  calc locM K m (φ (f p y)) = ((locM K m).comp φ) (f p y) := rfl
    _ = (μ.comp lam) (f p y) := by rw [h3]
    _ = μ (f p' y') := by rw [e1]; rfl
    _ = (μ.comp a) (f A u) := by rw [e2]; rfl
    _ = c (f A u) := by rw [h4]
end Formalism.L2.Pj
