-- Prove2me | solution 1 for BianchiIX.eventually_forall_movingInterval
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:42:45.854326+00:00
-- url     : https://prove2.me/submissions/8692500a-3c9a-4dd6-a492-8ff770f86962

import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith


namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {X : Type*} [TopologicalSpace X]


/-- Compactness remains uniform when the right endpoint varies continuously. -/
theorem solution {x₀ : X} {T : X → ℝ} {P : X → ℝ → Prop}
    (hT : ContinuousAt T x₀) (hpos : 0 < T x₀)
    (hP : ∀ t ∈ Icc 0 (T x₀), ∀ᶠ z : X × ℝ in 𝓝 (x₀, t), P z.1 z.2) :
    ∀ᶠ x in 𝓝 x₀, ∀ t ∈ Icc 0 (T x), P x t := by
  have H : ∀ᶠ x in 𝓝 x₀, ∀ u ∈ Icc (0 : ℝ) 1, P x (u * T x) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro u hu
    have ht : u * T x₀ ∈ Icc 0 (T x₀) :=
      ⟨mul_nonneg hu.1 hpos.le, by simpa using mul_le_mul_of_nonneg_right hu.2 hpos.le⟩
    have hc : ContinuousAt (fun z : X × ℝ => (z.1, z.2 * T z.1)) (x₀, u) :=
      continuousAt_fst.prodMk (continuousAt_snd.mul (hT.comp continuousAt_fst))
    exact hc.eventually (hP _ ht)
  have hp : ∀ᶠ x in 𝓝 x₀, 0 < T x := hT.eventually (isOpen_Ioi.mem_nhds hpos)
  filter_upwards [H, hp] with x hx hpx
  intro t ht
  have hu : t / T x ∈ Icc (0 : ℝ) 1 :=
    ⟨div_nonneg ht.1 hpx.le, (div_le_one hpx).mpr ht.2⟩
  simpa only [div_mul_cancel₀ _ (ne_of_gt hpx)] using hx _ hu
