-- Prove2me | solution 1 for DualSepClusterLP.separatorLocalSearch
-- status  : ACCEPTED   (prove)
-- author  : @hypercube
-- created : 2026-11-19T14:52:52.925004+00:00
-- url     : https://prove2.me/submissions/fe9bc198-ad49-4b76-a395-4f892c054165

import Mathlib
import Definitions.Def_DualSepClusterLP_SeparationChecks
import Definitions.Def_DualSepClusterLP_CutSearch
import Theorems.Thm_DualSepClusterLP_denseAffineApproximation

/-
Machine combinators from openai/math, commit 7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a, with Lean 4.33.1 compatibility edits.
                                 Apache License
                           Version 2.0, January 2004
                        http://www.apache.org/licenses/

   TERMS AND CONDITIONS FOR USE, REPRODUCTION, AND DISTRIBUTION

   1. Definitions.

      "License" shall mean the terms and conditions for use, reproduction,
      and distribution as defined by Sections 1 through 9 of this document.

      "Licensor" shall mean the copyright owner or entity authorized by
      the copyright owner that is granting the License.

      "Legal Entity" shall mean the union of the acting entity and all
      other entities that control, are controlled by, or are under common
      control with that entity. For the purposes of this definition,
      "control" means (i) the power, direct or indirect, to cause the
      direction or management of such entity, whether by contract or
      otherwise, or (ii) ownership of fifty percent (50%) or more of the
      outstanding shares, or (iii) beneficial ownership of such entity.

      "You" (or "Your") shall mean an individual or Legal Entity
      exercising permissions granted by this License.

      "Source" form shall mean the preferred form for making modifications,
      including but not limited to software source code, documentation
      source, and configuration files.

      "Object" form shall mean any form resulting from mechanical
      transformation or translation of a Source form, including but
      not limited to compiled object code, generated documentation,
      and conversions to other media types.

      "Work" shall mean the work of authorship, whether in Source or
      Object form, made available under the License, as indicated by a
      copyright notice that is included in or attached to the work
      (an example is provided in the Appendix below).

      "Derivative Works" shall mean any work, whether in Source or Object
      form, that is based on (or derived from) the Work and for which the
      editorial revisions, annotations, elaborations, or other modifications
      represent, as a whole, an original work of authorship. For the purposes
      of this License, Derivative Works shall not include works that remain
      separable from, or merely link (or bind by name) to the interfaces of,
      the Work and Derivative Works thereof.

      "Contribution" shall mean any work of authorship, including
      the original version of the Work and any modifications or additions
      to that Work or Derivative Works thereof, that is intentionally
      submitted to Licensor for inclusion in the Work by the copyright owner
      or by an individual or Legal Entity authorized to submit on behalf of
      the copyright owner. For the purposes of this definition, "submitted"
      means any form of electronic, verbal, or written communication sent
      to the Licensor or its representatives, including but not limited to
      communication on electronic mailing lists, source code control systems,
      and issue tracking systems that are managed by, or on behalf of, the
      Licensor for the purpose of discussing and improving the Work, but
      excluding communication that is conspicuously marked or otherwise
      designated in writing by the copyright owner as "Not a Contribution."

      "Contributor" shall mean Licensor and any individual or Legal Entity
      on behalf of whom a Contribution has been received by Licensor and
      subsequently incorporated within the Work.

   2. Grant of Copyright License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      copyright license to reproduce, prepare Derivative Works of,
      publicly display, publicly perform, sublicense, and distribute the
      Work and such Derivative Works in Source or Object form.

   3. Grant of Patent License. Subject to the terms and conditions of
      this License, each Contributor hereby grants to You a perpetual,
      worldwide, non-exclusive, no-charge, royalty-free, irrevocable
      (except as stated in this section) patent license to make, have made,
      use, offer to sell, sell, import, and otherwise transfer the Work,
      where such license applies only to those patent claims licensable
      by such Contributor that are necessarily infringed by their
      Contribution(s) alone or by combination of their Contribution(s)
      with the Work to which such Contribution(s) was submitted. If You
      institute patent litigation against any entity (including a
      cross-claim or counterclaim in a lawsuit) alleging that the Work
      or a Contribution incorporated within the Work constitutes direct
      or contributory patent infringement, then any patent licenses
      granted to You under this License for that Work shall terminate
      as of the date such litigation is filed.

   4. Redistribution. You may reproduce and distribute copies of the
      Work or Derivative Works thereof in any medium, with or without
      modifications, and in Source or Object form, provided that You
      meet the following conditions:

      (a) You must give any other recipients of the Work or
          Derivative Works a copy of this License; and

      (b) You must cause any modified files to carry prominent notices
          stating that You changed the files; and

      (c) You must retain, in the Source form of any Derivative Works
          that You distribute, all copyright, patent, trademark, and
          attribution notices from the Source form of the Work,
          excluding those notices that do not pertain to any part of
          the Derivative Works; and

      (d) If the Work includes a "NOTICE" text file as part of its
          distribution, then any Derivative Works that You distribute must
          include a readable copy of the attribution notices contained
          within such NOTICE file, excluding those notices that do not
          pertain to any part of the Derivative Works, in at least one
          of the following places: within a NOTICE text file distributed
          as part of the Derivative Works; within the Source form or
          documentation, if provided along with the Derivative Works; or,
          within a display generated by the Derivative Works, if and
          wherever such third-party notices normally appear. The contents
          of the NOTICE file are for informational purposes only and
          do not modify the License. You may add Your own attribution
          notices within Derivative Works that You distribute, alongside
          or as an addendum to the NOTICE text from the Work, provided
          that such additional attribution notices cannot be construed
          as modifying the License.

      You may add Your own copyright statement to Your modifications and
      may provide additional or different license terms and conditions
      for use, reproduction, or distribution of Your modifications, or
      for any such Derivative Works as a whole, provided Your use,
      reproduction, and distribution of the Work otherwise complies with
      the conditions stated in this License.

   5. Submission of Contributions. Unless You explicitly state otherwise,
      any Contribution intentionally submitted for inclusion in the Work
      by You to the Licensor shall be under the terms and conditions of
      this License, without any additional terms or conditions.
      Notwithstanding the above, nothing herein shall supersede or modify
      the terms of any separate license agreement you may have executed
      with Licensor regarding such Contributions.

   6. Trademarks. This License does not grant permission to use the trade
      names, trademarks, service marks, or product names of the Licensor,
      except as required for reasonable and customary use in describing the
      origin of the Work and reproducing the content of the NOTICE file.

   7. Disclaimer of Warranty. Unless required by applicable law or
      agreed to in writing, Licensor provides the Work (and each
      Contributor provides its Contributions) on an "AS IS" BASIS,
      WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or
      implied, including, without limitation, any warranties or conditions
      of TITLE, NON-INFRINGEMENT, MERCHANTABILITY, or FITNESS FOR A
      PARTICULAR PURPOSE. You are solely responsible for determining the
      appropriateness of using or redistributing the Work and assume any
      risks associated with Your exercise of permissions under this License.

   8. Limitation of Liability. In no event and under no legal theory,
      whether in tort (including negligence), contract, or otherwise,
      unless required by applicable law (such as deliberate and grossly
      negligent acts) or agreed to in writing, shall any Contributor be
      liable to You for damages, including any direct, indirect, special,
      incidental, or consequential damages of any character arising as a
      result of this License or out of the use or inability to use the
      Work (including but not limited to damages for loss of goodwill,
      work stoppage, computer failure or malfunction, or any and all
      other commercial damages or losses), even if such Contributor
      has been advised of the possibility of such damages.

   9. Accepting Warranty or Additional Liability. While redistributing
      the Work or Derivative Works thereof, You may choose to offer,
      and charge a fee for, acceptance of support, warranty, indemnity,
      or other liability obligations and/or rights consistent with this
      License. However, in accepting such obligations, You may act only
      on Your own behalf and on Your sole responsibility, not on behalf
      of any other Contributor, and only if You agree to indemnify,
      defend, and hold each Contributor harmless for any liability
      incurred by, or claims asserted against, such Contributor by reason
      of your accepting any such warranty or additional liability.

   END OF TERMS AND CONDITIONS

   APPENDIX: How to apply the Apache License to your work.

      To apply the Apache License to your work, attach the following
      boilerplate notice, with the fields enclosed by brackets "[]"
      replaced with your own identifying information. (Don't include
      the brackets!)  The text should be enclosed in the appropriate
      comment syntax for the file format. We also recommend that a
      file or class name and description of purpose be included on the
      same "printed page" as the copyright notice for easier
      identification within third-party archives.

   Copyright [yyyy] [name of copyright owner]

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.

-/

/- OAI.Combinatorics.KMedian.Binary.BooleanMachine -/
section
namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Turing StateTransition Function Finset

structure Machine where
  K : Type
  [decK : DecidableEq K]
  [finK : Fintype K]
  input : K
  output : K
  Label : Type
  [finLabel : Fintype Label]
  main : Label
  State : Type
  [finState : Fintype State]
  initial : State
  code : Label → TM2.Stmt (fun _ : K => Bool) Label State

attribute [instance] Machine.decK Machine.finK Machine.finLabel Machine.finState

namespace Machine

def tm (M : Machine) : FinTM2 where
  K := M.K
  k₀ := M.input
  k₁ := M.output
  Γ _ := Bool
  Λ := M.Label
  main := M.main
  σ := M.State
  initialState := M.initial
  m := M.code

instance allWorkFinite (M : Machine) (k : M.tm.K) : Fintype (M.tm.Γ k) :=
  inferInstanceAs (Fintype Bool)

abbrev Cfg (M : Machine) := TM2.Cfg (fun _ : M.K => Bool) M.Label M.State

def initialCfg (M : Machine) (s : List Bool) : M.Cfg :=
  ⟨some M.main, M.initial, fun k => if k=M.input then s else []⟩

def finalCfg (M : Machine) (s : List Bool) : M.Cfg :=
  ⟨none, M.initial, fun k => if k=M.output then s else []⟩

@[simp] theorem init_eq (M : Machine) (s : List Bool) :
    initList M.tm s=M.initialCfg s := by
  rfl

@[simp] theorem halt_eq (M : Machine) (s : List Bool) :
    haltList M.tm s=M.finalCfg s := by
  rfl

abbrev step (M : Machine) : M.Cfg → Option M.Cfg := TM2.step M.code

end Machine

theorem cfg_ext {K L S : Type} {a b : TM2.Cfg (fun _ : K => Bool) L S}
    (hl : a.l=b.l) (hv : a.var=b.var) (hs : a.stk=b.stk) : a=b := by
  cases a
  cases b
  cases hl
  cases hv
  cases hs
  rfl

inductive Trace {α : Type*} (f : α → Option α) : ℕ → α → α → Prop
  | refl (a : α) : Trace f 0 a a
  | cons {n : ℕ} {a b c : α} : f a=some b → Trace f n b c → Trace f (n+1) a c

namespace Trace
variable {α β : Type*} {f : α → Option α}

theorem trans {n m : ℕ} {a b c : α} (h : Trace f n a b) (g : Trace f m b c) :
    Trace f (n+m) a c := by
  induction h with
  | refl => simpa using g
  | cons hs ht ih => simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using cons hs (ih g)

theorem map {g : β → Option β} (e : α → β)
    (he : ∀ a b, f a=some b → g (e a)=some (e b))
    {n : ℕ} {a b : α} (h : Trace f n a b) : Trace g n (e a) (e b) := by
  induction h with
  | refl => exact refl _
  | cons hs _ ih => exact cons (he _ _ hs) ih

theorem iterate_eq {n : ℕ} {a b : α} (h : Trace f n a b) :
    (flip bind f)^[n] (some a)=some b := by
  induction h with
  | refl => rfl
  | cons hs ht ih =>
      rw [Function.iterate_succ_apply,show (flip bind f) (some _)=_ from hs]
      exact ih

theorem of_iterate {n : ℕ} {a b : α}
    (h : (flip bind f)^[n] (some a)=some b) : Trace f n a b := by
  induction n generalizing a with
  | zero =>
      have hab : a=b := Option.some.inj h
      subst b
      exact refl a
  | succ n ih =>
      rw [Function.iterate_succ_apply] at h
      cases hc : f a with
      | none =>
          have hz : ∀ t : ℕ, (flip bind f)^[t] (none : Option α)=none := by
            intro t
            induction t with
            | zero => rfl
            | succ t iht =>
                rw [Function.iterate_succ_apply]
                exact iht
          change (flip bind f)^[n] (f a)=some b at h
          rw [hc,hz] at h
          contradiction
      | some c =>
          have hh : (flip bind f)^[n] (some c)=some b := by
            change (flip bind f)^[n] (f a)=some b at h
            rwa [hc] at h
          exact cons hc (ih hh)

def inTime {n : ℕ} {a b : α} (h : Trace f n a b) :
    EvalsToInTime f a (some b) n := ⟨⟨n,h.iterate_eq⟩,le_rfl⟩

theorem of_inTime {n : ℕ} {a b : α} (h : EvalsToInTime f a (some b) n) :
    Trace f h.steps a b := of_iterate h.evals_in_steps

end Trace

namespace Machine
variable {K L S : Type} [DecidableEq K]

def pushes : TM2.Stmt (fun _ : K => Bool) L S → ℕ
  | .push _ _ q => 1+pushes q
  | .peek _ _ q => pushes q
  | .pop _ _ q => pushes q
  | .load _ q => pushes q
  | .branch _ q r => max (pushes q) (pushes r)
  | .goto _ => 0
  | .halt => 0

def volume [Fintype K] (s : K → List Bool) : ℕ := ∑ k, (s k).length

variable [Fintype K]

theorem volume_update (s : K → List Bool) (k : K) (v : List Bool) :
    volume (update s k v)+(s k).length=volume s+v.length := by
  classical
  unfold volume
  have he : (fun j => (update s k v j).length)=update (fun j => (s j).length) k v.length := by
    funext j
    simp only [update_apply]
    split <;> rfl
  rw [he,Finset.sum_update_of_mem (mem_univ k)]
  have hh := Finset.sum_erase_add (univ : Finset K) (fun j => (s j).length) (mem_univ k)
  simp only [Finset.sdiff_singleton_eq_erase]
  omega

theorem stepAux_volume (q : TM2.Stmt (fun _ : K => Bool) L S)
    (v : S) (s : K → List Bool) :
    volume (TM2.stepAux q v s).stk ≤ volume s+pushes q := by
  induction q generalizing v s with
  | push k g q ih =>
      have h := ih v (update s k (g v::s k))
      have hv := volume_update s k (g v::s k)
      simp only [List.length_cons] at hv
      simpa only [TM2.stepAux,pushes,Nat.add_assoc] using (by omega :
        volume (TM2.stepAux q v (update s k (g v::s k))).stk≤volume s+(1+pushes q))
  | peek k g q ih => exact ih _ _
  | pop k g q ih =>
      have h := ih (g v (s k).head?) (update s k (s k).tail)
      have hv := volume_update s k (s k).tail
      have hl := List.length_tail (l := s k)
      simp only [TM2.stepAux,pushes]
      omega
  | load g q ih => exact ih _ _
  | branch g q r ihq ihr =>
      cases hg : g v
      · simpa only [TM2.stepAux,hg,Bool.false_eq_true,Bool.cond_false,pushes] using
          (ihr v s).trans (Nat.add_le_add_left (le_max_right (pushes q) _) _)
      · simpa only [TM2.stepAux,hg,Bool.cond_true,pushes] using
          (ihq v s).trans (Nat.add_le_add_left (le_max_left _ (pushes r)) _)
  | goto g => simp only [TM2.stepAux,pushes,Nat.add_zero,le_refl]
  | halt => simp only [TM2.stepAux,pushes,Nat.add_zero,le_refl]

def growth (M : Machine) : ℕ := ∑ l, pushes (M.code l)

theorem step_volume (M : Machine) (a b : M.Cfg) (h : M.step a=some b) :
    volume b.stk ≤ volume a.stk+M.growth := by
  rcases a with ⟨l,v,s⟩
  cases l with
  | none => cases h
  | some l =>
      have hb : b=TM2.stepAux (M.code l) v s := (Option.some.inj h).symm
      rw [hb]
      exact (stepAux_volume _ _ _).trans (Nat.add_le_add_left
        (show pushes (M.code l) ≤ M.growth from
          single_le_sum (f:=fun x => pushes (M.code x)) (fun _ _ => Nat.zero_le _) (mem_univ l)) _)

theorem trace_volume (M : Machine) {n : ℕ} {a b : M.Cfg}
    (h : Trace M.step n a b) : volume b.stk ≤ volume a.stk+n*M.growth := by
  induction h with
  | refl => simp
  | @cons n a b c hab hbc ih =>
      have hs := M.step_volume a b hab
      calc
        _ ≤ volume b.stk+n*M.growth := ih
        _ ≤ volume a.stk+(n+1)*M.growth := by rw [Nat.add_mul]; omega

@[simp] theorem initial_volume (M : Machine) (s : List Bool) :
    volume (M.initialCfg s).stk=s.length := by
  classical
  simp only [initialCfg,volume,apply_ite List.length,List.length_nil]
  simp

@[simp] theorem final_volume (M : Machine) (s : List Bool) :
    volume (M.finalCfg s).stk=s.length := by
  classical
  simp only [finalCfg,volume,apply_ite List.length,List.length_nil]
  simp

theorem output_length (M : Machine) {s t : List Bool} {n : ℕ}
    (h : TM2OutputsInTime M.tm s (some t) n) : t.length ≤ s.length+n*M.growth := by
  have ht : Trace M.step h.steps (M.initialCfg s) (M.finalCfg t) :=
    Trace.of_iterate h.evals_in_steps
  have hv := M.trace_volume ht
  simp only [initial_volume,final_volume] at hv
  exact hv.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ h.steps_le_m) _)

end Machine
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanEmbedding -/
section
namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Turing Function

structure Embedding (K L S K' L' S' : Type) [DecidableEq K] [DecidableEq K'] where
  key : K → K'
  read : S' → S
  write : S' → S → S'
  state : S → S'
  read_state : ∀ v, read (state v)=v
  write_state : ∀ v w, write (state v) w=state w
  stack : (K → List Bool) → K' → List Bool
  stack_key : ∀ s k, stack s (key k)=s k
  stack_update : ∀ s k x, stack (update s k x)=update (stack s) (key k) x
  label : L → L'
  halted : Option L'
  stop : TM2.Stmt (fun _ : K' => Bool) L' S'
  stop_spec : ∀ v s, TM2.stepAux stop (state v) (stack s)=⟨halted,state v,stack s⟩

namespace Embedding
variable {K L S K' L' S' : Type} [DecidableEq K] [DecidableEq K']
variable (E : Embedding K L S K' L' S')

def stmt : TM2.Stmt (fun _ : K => Bool) L S → TM2.Stmt (fun _ : K' => Bool) L' S'
  | .push k f q => .push (E.key k) (fun v => f (E.read v)) (stmt q)
  | .peek k f q => .peek (E.key k) (fun v x => E.write v (f (E.read v) x)) (stmt q)
  | .pop k f q => .pop (E.key k) (fun v x => E.write v (f (E.read v) x)) (stmt q)
  | .load f q => .load (fun v => E.write v (f (E.read v))) (stmt q)
  | .branch f q r => .branch (fun v => f (E.read v)) (stmt q) (stmt r)
  | .goto f => .goto (fun v => E.label (f (E.read v)))
  | .halt => E.stop

def cfg (a : TM2.Cfg (fun _ : K => Bool) L S) : TM2.Cfg (fun _ : K' => Bool) L' S' :=
  ⟨a.l.elim E.halted (fun l => some (E.label l)),E.state a.var,E.stack a.stk⟩

theorem stepAux_stmt (q : TM2.Stmt (fun _ : K => Bool) L S) (v : S) (s : K → List Bool) :
    TM2.stepAux (E.stmt q) (E.state v) (E.stack s)=E.cfg (TM2.stepAux q v s) := by
  induction q generalizing v s with
  | push k f q ih =>
      simp only [stmt,TM2.stepAux,E.read_state,E.stack_key,← E.stack_update]
      exact ih _ _
  | peek k f q ih =>
      simp only [stmt,TM2.stepAux,E.read_state,E.stack_key,E.write_state]
      exact ih _ _
  | pop k f q ih =>
      simp only [stmt,TM2.stepAux,E.read_state,E.stack_key,E.write_state,← E.stack_update]
      exact ih _ _
  | load f q ih =>
      simp only [stmt,TM2.stepAux,E.read_state,E.write_state]
      exact ih _ _
  | branch f q r ihq ihr =>
      cases h : f v <;> simp only [stmt,TM2.stepAux,E.read_state,h,Bool.cond_false,Bool.cond_true]
      · exact ihr _ _
      · exact ihq _ _
  | goto f => simp only [stmt,TM2.stepAux,E.read_state,cfg,Option.elim_some]
  | halt => exact E.stop_spec v s

theorem step_cfg (m : L → TM2.Stmt (fun _ : K => Bool) L S)
    (m' : L' → TM2.Stmt (fun _ : K' => Bool) L' S')
    (hm : ∀ l, m' (E.label l)=E.stmt (m l))
    (a b : TM2.Cfg (fun _ : K => Bool) L S) (h : TM2.step m a=some b) :
    TM2.step m' (E.cfg a)=some (E.cfg b) := by
  rcases a with ⟨l,v,s⟩
  cases l with
  | none => cases h
  | some l =>
      have hb : b=TM2.stepAux (m l) v s := (Option.some.inj h).symm
      subst b
      simp only [cfg,Option.elim_some,TM2.step,hm]
      exact congrArg some (E.stepAux_stmt (m l) v s)

theorem trace (m : L → TM2.Stmt (fun _ : K => Bool) L S)
    (m' : L' → TM2.Stmt (fun _ : K' => Bool) L' S')
    (hm : ∀ l, m' (E.label l)=E.stmt (m l))
    {n : ℕ} {a b : TM2.Cfg (fun _ : K => Bool) L S} (h : Trace (TM2.step m) n a b) :
    Trace (TM2.step m') n (E.cfg a) (E.cfg b) :=
  h.map E.cfg (E.step_cfg m m' hm)

end Embedding
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanComposition -/
section
namespace OAI


                                          
section
namespace MetricKMedian.Binary
open Turing Function

namespace Compose
variable (M N : Machine)

abbrev Key := M.K ⊕ (Unit ⊕ N.K)
abbrev Label := M.Label ⊕ (Bool ⊕ N.Label)
abbrev State := M.State × N.State × Option Bool

abbrev phaseLabel (b : Bool) : Label M N := .inr (.inl b)
abbrev auxiliary : Key M N := .inr (.inl ())

def left : Embedding M.K M.Label M.State (Key M N) (Label M N) (State M N) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,N.initial,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim s (fun _ => [])
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j
    · simp only [update_apply,Sum.elim_inl,Sum.inl.injEq]
    · simp only [update_apply,Sum.elim_inr,Sum.inr_ne_inl,ite_false]
  label := Sum.inl
  halted := some (phaseLabel M N false)
  stop := .goto (fun _ => phaseLabel M N false)
  stop_spec _ _ := rfl

def right : Embedding N.K N.Label N.State (Key M N) (Label M N) (State M N) where
  key k := .inr (.inr k)
  read v := v.2.1
  write v x := (v.1,x,v.2.2)
  state v := (M.initial,v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim (fun _ => []) (Sum.elim (fun _ => []) s)
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j
    · simp only [update_apply,Sum.elim_inl,Sum.inl_ne_inr,ite_false]
    · rcases j with j | j <;> simp only [update_apply,Sum.elim_inl,Sum.elim_inr,Sum.inr.injEq,Sum.inl_ne_inr,ite_false]
  label l := .inr (.inr l)
  halted := none
  stop := .halt
  stop_spec _ _ := rfl

def source (b : Bool) : Key M N := if b then auxiliary M N else .inl M.output

def target (b : Bool) : Key M N := if b then .inr (.inr N.input) else auxiliary M N

 theorem source_ne_target (b : Bool) : source M N b ≠ target M N b := by
  cases b <;> simp [source,target,auxiliary]

def following (b : Bool) : Label M N :=
  if b then .inr (.inr N.main) else phaseLabel M N true

def clean (v : State M N) : State M N := (v.1,v.2.1,none)

def transfer (b : Bool) : TM2.Stmt (fun _ : Key M N => Bool) (Label M N) (State M N) :=
  .pop (source M N b) (fun v c => (v.1,v.2.1,c))
    (.branch (fun v => v.2.2.isSome)
      (.push (target M N b) (fun v => v.2.2.getD false)
        (.load (clean M N) (.goto (fun _ => phaseLabel M N b))))
      (.load (clean M N) (.goto (fun _ => following M N b))))

def code : Label M N → TM2.Stmt (fun _ : Key M N => Bool) (Label M N) (State M N)
  | .inl l => (left M N).stmt (M.code l)
  | .inr (.inl b) => transfer M N b
  | .inr (.inr l) => (right M N).stmt (N.code l)

abbrev machine : Machine where
  K := Key M N
  input := .inl M.input
  output := .inr (.inr N.output)
  Label := Label M N
  main := .inl M.main
  State := State M N
  initial := (M.initial,N.initial,none)
  code := code M N

 theorem code_left (l : M.Label) : (machine M N).code ((left M N).label l)=
    (left M N).stmt (M.code l) := rfl

 theorem code_right (l : N.Label) : (machine M N).code ((right M N).label l)=
    (right M N).stmt (N.code l) := rfl

 theorem initial_left (s : List Bool) : (left M N).cfg (M.initialCfg s)=
    (machine M N).initialCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Embedding.cfg,left,Machine.initialCfg,machine]

 theorem final_right (s : List Bool) : (right M N).cfg (N.finalCfg s)=
    (machine M N).finalCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,right,Machine.finalCfg,machine]
  · rcases k with k | k <;> simp [Embedding.cfg,right,Machine.finalCfg,machine]

end Compose

def twoStacks {K : Type} [DecidableEq K] (a b : K) (xs ys : List Bool) (k : K) : List Bool :=
  if k=a then xs else if k=b then ys else []

@[simp] theorem twoStacks_source {K : Type} [DecidableEq K] (a b : K) (xs ys : List Bool) :
    twoStacks a b xs ys a=xs := by simp [twoStacks]

@[simp] theorem twoStacks_target {K : Type} [DecidableEq K] {a b : K} (h : a≠b)
    (xs ys : List Bool) : twoStacks a b xs ys b=ys := by simp [twoStacks,h.symm]

 theorem twoStacks_move {K : Type} [DecidableEq K] {a b : K} (h : a≠b)
    (x : Bool) (xs ys : List Bool) :
    update (update (twoStacks a b (x::xs) ys) a xs) b (x::ys)=twoStacks a b xs (x::ys) := by
  funext k
  by_cases ha : k=a
  · subst k; simp [h,twoStacks]
  · by_cases hb : k=b
    · subst k; simp [h.symm,twoStacks]
    · simp [ha,hb,twoStacks]

 theorem twoStacks_pop_empty {K : Type} [DecidableEq K] (a b : K) (ys : List Bool) :
    update (twoStacks a b [] ys) a []=twoStacks a b [] ys := by
  funext k
  by_cases h : k=a <;> simp [twoStacks,h]

namespace Compose
variable (M N : Machine)

def transferCfg (b : Bool) (xs ys : List Bool) : (machine M N).Cfg :=
  ⟨some (phaseLabel M N b), (M.initial,N.initial,none),
    twoStacks (source M N b) (target M N b) xs ys⟩

 theorem transfer_cons (b x : Bool) (xs ys : List Bool) :
    (machine M N).step (transferCfg M N b (x::xs) ys)=
      some (transferCfg M N b xs (x::ys)) := by
  change some (TM2.stepAux (transfer M N b) (M.initial,N.initial,none)
    (twoStacks (source M N b) (target M N b) (x::xs) ys))=some (transferCfg M N b xs (x::ys))
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some,clean]
  rw [update_of_ne (Ne.symm (source_ne_target M N b)),twoStacks_target (source_ne_target M N b)]
  rw [twoStacks_move (source_ne_target M N b)]
  rfl

 theorem transfer_run (b : Bool) (xs ys : List Bool) :
    Trace (machine M N).step xs.length (transferCfg M N b xs ys)
      (transferCfg M N b [] (xs.reverse++ys)) := by
  induction xs generalizing ys with
  | nil => exact Trace.refl _
  | cons x xs ih =>
      have h := Trace.cons (transfer_cons M N b x xs ys) (ih (x::ys))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem transfer_empty (b : Bool) (ys : List Bool) :
    (machine M N).step (transferCfg M N b [] ys)=
      some ⟨some (following M N b),(M.initial,N.initial,none),
        twoStacks (source M N b) (target M N b) [] ys⟩ := by
  change some (TM2.stepAux (transfer M N b) (M.initial,N.initial,none)
    (twoStacks (source M N b) (target M N b) [] ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,clean,twoStacks_pop_empty]

 theorem left_final_transfer (xs : List Bool) :
    (left M N).cfg (M.finalCfg xs)=transferCfg M N false xs [] := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,left,Machine.finalCfg,transferCfg,twoStacks,source,target,auxiliary,Sum.inl.injEq,Sum.inl_ne_inr]
  · rcases k with k | k <;>
      simp [Embedding.cfg,left,Machine.finalCfg,transferCfg,twoStacks,source,target,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_change (ys : List Bool) :
    (machine M N).step (transferCfg M N false [] ys)=some (transferCfg M N true ys []) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [transferCfg,source,target,twoStacks,auxiliary,Sum.inl.injEq,Sum.inl_ne_inr]
  · rcases k with k | k <;> simp [transferCfg,source,target,twoStacks,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_end (ys : List Bool) :
    (machine M N).step (transferCfg M N true [] ys)=some ((right M N).cfg (N.initialCfg ys)) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k
  · simp [Embedding.cfg,right,Machine.initialCfg,source,target,twoStacks,auxiliary,Sum.inl_ne_inr]
  · rcases k with k | k <;>
      simp [Embedding.cfg,right,Machine.initialCfg,source,target,twoStacks,auxiliary,Sum.inr.injEq,Sum.inr_ne_inl]

 theorem transfer_full (xs : List Bool) :
    Trace (machine M N).step (2*xs.length+2)
      ((left M N).cfg (M.finalCfg xs)) ((right M N).cfg (N.initialCfg xs)) := by
  rw [left_final_transfer]
  have h₁ := transfer_run M N false xs []
  simp only [List.append_nil] at h₁
  have h₂ := Trace.cons (transfer_change M N xs.reverse) (transfer_run M N true xs.reverse [])
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h₂
  have h₃ := Trace.cons (transfer_end M N xs) (Trace.refl _)
  have hh := (h₁.trans h₂).trans h₃
  simpa only [show xs.length+(xs.length+1)+(0+1)=2*xs.length+2 by omega] using hh

 theorem run {s t u : List Bool} {n m : ℕ}
    (hM : Trace M.step n (M.initialCfg s) (M.finalCfg t))
    (hN : Trace N.step m (N.initialCfg t) (N.finalCfg u)) :
    Trace (machine M N).step (n+2*t.length+2+m)
      ((machine M N).initialCfg s) ((machine M N).finalCfg u) := by
  have h₁ := (left M N).trace M.code (machine M N).code (code_left M N) hM
  have h₂ := (right M N).trace N.code (machine M N).code (code_right M N) hN
  rw [initial_left] at h₁
  rw [final_right] at h₂
  have hh := (h₁.trans (transfer_full M N t)).trans h₂
  simpa only [Machine.step,machine,Nat.add_assoc] using hh

end Compose
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanPolynomial -/
section
namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Polynomial

 theorem polynomial_eval_mono (p : Polynomial ℕ) {a b : ℕ} (h : a ≤ b) :
    p.eval a ≤ p.eval b := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using Nat.add_le_add hp hq
  | monomial n x =>
      simpa only [Polynomial.eval_monomial] using Nat.mul_le_mul_left x (Nat.pow_le_pow_left h n)

structure PolyProgram {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (f : α → β) where
  machine : Machine
  time : Polynomial ℕ
  outputs : ∀ a, TM2OutputsInTime machine.tm (ea a) (some (eb (f a))) (time.eval (ea a).length)

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
variable {f : α → β} {g : β → γ}

def stock (P : PolyProgram ea eb f) : TM2ComputableInPolyTime ea eb f where
  tm := P.machine.tm
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := P.time
  outputsFun a := by
    have h := P.outputs a
    dsimp only [Machine.tm,Equiv.refl] at h ⊢
    simpa only [List.map_id] using h

 theorem finite_work (P : PolyProgram ea eb f) (k : P.stock.tm.K) : Finite (P.stock.tm.Γ k) :=
  inferInstanceAs (Finite Bool)

 noncomputable def sizeBound (P : PolyProgram ea eb f) : Polynomial ℕ :=
  X+P.time*C P.machine.growth

 theorem length_bound (P : PolyProgram ea eb f) (a : α) :
    (eb (f a)).length ≤ P.sizeBound.eval (ea a).length := by
  simpa only [sizeBound,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C]
    using P.machine.output_length (P.outputs a)

 noncomputable def compTime (P : PolyProgram ea eb f) (Q : PolyProgram eb ec g) : Polynomial ℕ :=
  P.time+2*P.sizeBound+2+Q.time.comp P.sizeBound

 noncomputable def comp (P : PolyProgram ea eb f) (Q : PolyProgram eb ec g) : PolyProgram ea ec (g ∘ f) where
  machine := Compose.machine P.machine Q.machine
  time := P.compTime Q
  outputs a := by
    let hP := P.outputs a
    let hQ := Q.outputs (f a)
    have tP : Trace P.machine.step hP.steps (P.machine.initialCfg (ea a))
        (P.machine.finalCfg (eb (f a))) := Trace.of_iterate hP.evals_in_steps
    have tQ : Trace Q.machine.step hQ.steps (Q.machine.initialCfg (eb (f a)))
        (Q.machine.finalCfg (ec (g (f a)))) := Trace.of_iterate hQ.evals_in_steps
    have h := Compose.run P.machine Q.machine tP tQ
    refine ⟨⟨_,h.iterate_eq⟩,?_⟩
    have hl := P.length_bound a
    have hqp := (hQ.steps_le_m).trans (polynomial_eval_mono Q.time hl)
    have hpp := hP.steps_le_m
    simp only [compTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,
      Polynomial.eval_comp]
    omega

 def congr (P : PolyProgram ea eb f) (f' : α → β) (h : ∀ a, f a=f' a) : PolyProgram ea eb f' where
  machine := P.machine
  time := P.time
  outputs a := by rw [← h a]; exact P.outputs a

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanTransducer -/
section
namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Turing Function Polynomial Finset

structure Transducer where
  Q : Type
  [finiteQ : Fintype Q]
  initial : Q
  next : Q → Bool → Q × List Bool
  finish : Q → List Bool
attribute [instance] Transducer.finiteQ

namespace Transducer
variable (T : Transducer)

def run : T.Q → List Bool → List Bool
  | q, [] => T.finish q
  | q, b::xs => (T.next q b).2 ++ run (T.next q b).1 xs

def width : ℕ := max (univ.sup (fun q => (T.finish q).length))
  (univ.sup (fun x : T.Q × Bool => (T.next x.1 x.2).2.length))

 theorem finish_length (q : T.Q) : (T.finish q).length ≤ T.width :=
  (le_sup (f:=fun q => (T.finish q).length) (mem_univ q)).trans (Nat.le_max_left _ _)

 theorem next_length (q : T.Q) (b : Bool) : (T.next q b).2.length ≤ T.width :=
  (le_sup (f:=fun x : T.Q × Bool => (T.next x.1 x.2).2.length) (mem_univ (q,b))).trans (Nat.le_max_right _ _)

 theorem run_length (q : T.Q) (xs : List Bool) : (T.run q xs).length ≤ T.width*(xs.length+1) := by
  induction xs generalizing q with
  | nil => simpa only [run,List.length_nil,zero_add,mul_one] using T.finish_length q
  | cons b xs ih =>
      have hn := T.next_length q b
      have ht := ih (T.next q b).1
      simp only [run,List.length_append,List.length_cons]
      rw [show xs.length+1+1=(xs.length+1)+1 by rfl,Nat.mul_add,mul_one]
      omega

inductive Key | input | buffer | output deriving DecidableEq
instance : Fintype Key := ⟨{Key.input,Key.buffer,Key.output},by
  intro k
  cases k <;> simp⟩
open Key
abbrev Label := T.Q ⊕ Unit
abbrev State := Option Bool

def emit : List Bool → TM2.Stmt (fun _ : Key => Bool) (Label T) State →
    TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | [], q => q
  | b::bs, q => .push buffer (fun _ => b) (emit bs q)

 theorem emit_step (bits : List Bool) (q : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (s : Key → List Bool) :
    TM2.stepAux (emit T bits q) v s=
      TM2.stepAux q v (update s buffer (bits.reverse++s buffer)) := by
  induction bits generalizing s with
  | nil => simp only [emit,List.reverse_nil,List.nil_append,update_eq_self]
  | cons b bs ih =>
      simp only [emit,TM2.stepAux,ih,update_self,update_idem,List.reverse_cons]
      simp only [List.append_assoc,List.singleton_append]

def transfer : TM2.Stmt (fun _ : Key => Bool) (Label T) State :=
  .pop buffer (fun _ b => b)
    (.branch Option.isSome
      (.push output (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => .inr ()))))
      (.load (fun _ => none) .halt))

def code : Label T → TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | .inl q => .pop input (fun _ b => b)
      (.branch Option.isSome
        (.branch (fun b => b.getD false)
          (.load (fun _ => none) (emit T (T.next q true).2 (.goto (fun _ => .inl (T.next q true).1))))
          (.load (fun _ => none) (emit T (T.next q false).2 (.goto (fun _ => .inl (T.next q false).1)))))
        (.load (fun _ => none) (emit T (T.finish q) (.goto (fun _ => .inr ())))))
  | .inr _ => transfer T

abbrev machine : Machine where
  K := Key
  input := input
  output := output
  Label := Label T
  main := .inl T.initial
  State := State
  initial := none
  code := code T

def store (xs ys zs : List Bool) : Key → List Bool
  | input => xs
  | buffer => ys
  | output => zs

 theorem stacks_update_input (xs ys zs ts : List Bool) :
    update (store xs ys zs) input ts=store ts ys zs := by
  funext k
  cases k <;> simp [store]

 theorem stacks_update_buffer (xs ys zs ts : List Bool) :
    update (store xs ys zs) buffer ts=store xs ts zs := by
  funext k
  cases k <;> simp [store]

 theorem stacks_update_output (xs ys zs ts : List Bool) :
    update (store xs ys zs) output ts=store xs ys ts := by
  funext k
  cases k <;> simp [store]

def readCfg (q : T.Q) (xs ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inl q),none,store xs ys []⟩

def transferCfg (ys zs : List Bool) : (machine T).Cfg :=
  ⟨some (.inr ()),none,store [] ys zs⟩

 theorem read_cons (q : T.Q) (b : Bool) (xs ys : List Bool) :
    (machine T).step (T.readCfg q (b::xs) ys)=
      some (T.readCfg (T.next q b).1 xs ((T.next q b).2.reverse++ys)) := by
  cases b <;>
    simp [readCfg,TM2.step,code,TM2.stepAux,store,List.head?,List.tail,
      emit_step,stacks_update_input,stacks_update_buffer]

 theorem read_nil (q : T.Q) (ys : List Bool) :
    (machine T).step (T.readCfg q [] ys)=some (T.transferCfg ((T.finish q).reverse++ys) []) := by
  simp [readCfg,transferCfg,TM2.step,code,TM2.stepAux,store,List.head?,List.tail,
    emit_step,stacks_update_input,stacks_update_buffer]

 theorem read_run (q : T.Q) (xs ys : List Bool) :
    Trace (machine T).step (xs.length+1) (T.readCfg q xs ys)
      (T.transferCfg ((T.run q xs).reverse++ys) []) := by
  induction xs generalizing q ys with
  | nil => exact Trace.cons (T.read_nil q ys) (Trace.refl _)
  | cons b xs ih =>
      have h := Trace.cons (T.read_cons q b xs ys) (ih (T.next q b).1 ((T.next q b).2.reverse++ys))
      simpa only [run,List.reverse_append,List.append_assoc,List.length_cons] using h

 theorem transfer_cons (b : Bool) (ys zs : List Bool) :
    (machine T).step (T.transferCfg (b::ys) zs)=some (T.transferCfg ys (b::zs)) := by
  simp [transferCfg,TM2.step,code,transfer,TM2.stepAux,store,List.head?,List.tail,
    stacks_update_buffer,stacks_update_output]

 theorem transfer_nil (zs : List Bool) :
    (machine T).step (T.transferCfg [] zs)=some ((machine T).finalCfg zs) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    cases k <;> simp [Machine.finalCfg,code,transfer,TM2.stepAux,store]

 theorem transfer_run (ys zs : List Bool) :
    Trace (machine T).step (ys.length+1) (T.transferCfg ys zs)
      ((machine T).finalCfg (ys.reverse++zs)) := by
  induction ys generalizing zs with
  | nil => exact Trace.cons (T.transfer_nil zs) (Trace.refl _)
  | cons b ys ih =>
      have h := Trace.cons (T.transfer_cons b ys zs) (ih (b::zs))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem run_trace (xs : List Bool) :
    Trace (machine T).step (xs.length+(T.run T.initial xs).length+2)
      ((machine T).initialCfg xs) ((machine T).finalCfg (T.run T.initial xs)) := by
  have hi : (machine T).initialCfg xs=T.readCfg T.initial xs [] := by
    apply cfg_ext <;> try rfl
    funext k
    cases k <;> simp [Machine.initialCfg,readCfg,store]
  rw [hi]
  have hr := T.read_run T.initial xs []
  simp only [List.append_nil] at hr
  have h := hr.trans (T.transfer_run (T.run T.initial xs).reverse [])
  simpa only [List.append_nil,List.length_reverse,List.reverse_reverse,
    show xs.length+1+((T.run T.initial xs).length+1)=xs.length+(T.run T.initial xs).length+2 by omega] using h

noncomputable def program : PolyProgram id id (T.run T.initial) where
  machine := machine T
  time := C (T.width+1)*X+C (T.width+2)
  outputs xs := by
    refine ⟨⟨_,(T.run_trace xs).iterate_eq⟩,?_⟩
    have hl := T.run_length T.initial xs
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,id_eq]
    nlinarith

end Transducer
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanEncoding -/
section
namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

def quote : List Bool → List Bool
  | [] => [false]
  | b::bs => true::b::quote bs

@[simp] theorem quote_length (bs : List Bool) : (quote bs).length=2*bs.length+1 := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [quote,List.length_cons,ih]; omega

def encodePair {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (x : α × β) : List Bool :=
  quote (ea x.1)++eb x.2

@[simp] theorem encodePair_length {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (x : α × β) :
    (encodePair ea eb x).length=2*(ea x.1).length+1+(eb x.2).length := by
  simp only [encodePair,List.length_append,quote_length]

namespace WordTransducer

def quoting : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[true,b])
  finish _ := [false]

 theorem quoting_run (xs : List Bool) : quoting.run () xs=quote xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [Transducer.run,quoting,List.cons_append,List.nil_append,quote] using congrArg (fun l => true::b::l) ih

def projecting (tail : Bool) : Transducer where
  Q := Option Bool
  initial := none
  next q b := match q with
    | none => (some (!b),[])
    | some false => (none,if tail then [] else [b])
    | some true => (some true,if tail then [b] else [])
  finish _ := []

 theorem projecting_done (tail : Bool) (xs : List Bool) :
    (projecting tail).run (some true) xs=if tail then xs else [] := by
  induction xs with
  | nil => cases tail <;> rfl
  | cons b xs ih =>
      change (if tail then [b] else [])++(projecting tail).run (some true) xs=_
      rw [ih]
      cases tail <;> simp

 theorem projecting_pair (tail : Bool) (xs ys : List Bool) :
    (projecting tail).run none (quote xs++ys)=if tail then ys else xs := by
  induction xs with
  | nil => exact projecting_done tail ys
  | cons b xs ih =>
      change (if tail then [] else [b])++(projecting tail).run none (quote xs++ys)=_
      rw [ih]
      cases tail <;> simp

end WordTransducer

namespace PolyProgram

 def of_word {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
    {g : List Bool → List Bool} (P : PolyProgram id id g)
    (h : ∀ a, g (ea a)=eb (f a)) : PolyProgram ea eb f where
  machine := P.machine
  time := P.time
  outputs a := by simpa only [id_eq,h a] using P.outputs (ea a)

 noncomputable def quote : PolyProgram id id Binary.quote :=
  WordTransducer.quoting.program.congr _ WordTransducer.quoting_run

 noncomputable def fst {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) ea Prod.fst :=
  (WordTransducer.projecting false).program.of_word (fun _ => by
    simpa only [encodePair,Bool.false_eq_true,ite_false,WordTransducer.projecting] using WordTransducer.projecting_pair false _ _)

 noncomputable def snd {α β : Type} (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) eb Prod.snd :=
  (WordTransducer.projecting true).program.of_word (fun _ => by
    simpa only [encodePair,ite_true,WordTransducer.projecting] using WordTransducer.projecting_pair true _ _)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanThread -/
section
namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace Thread
variable (M : Machine)
abbrev Key := M.K ⊕ Bool
abbrev Label := M.Label ⊕ Fin 4
abbrev State := M.State × Option Bool
abbrev source : Key M := .inr false
abbrev buffer : Key M := .inr true
abbrev reading : Label M := .inr 0
abbrev loading : Label M := .inr 1
abbrev emitting : Label M := .inr 2
abbrev draining : Label M := .inr 3

def store (s : M.K → List Bool) (xs ys : List Bool) : Key M → List Bool :=
  fun k => match k with
  | .inl k => s k
  | .inr false => xs
  | .inr true => ys

@[simp] theorem store_local (s : M.K → List Bool) (xs ys : List Bool) (k : M.K) :
    store M s xs ys (.inl k)=s k := rfl
@[simp] theorem store_source (s : M.K → List Bool) (xs ys : List Bool) :
    store M s xs ys (source M)=xs := rfl
@[simp] theorem store_buffer (s : M.K → List Bool) (xs ys : List Bool) :
    store M s xs ys (buffer M)=ys := rfl

def slot (k : M.K) (xs : List Bool) : M.K → List Bool := fun j => if j=k then xs else []

 theorem slot_nil (k : M.K) : slot M k []=fun _ => [] := by funext j; simp [slot]
 theorem slot_self (k : M.K) (xs : List Bool) : slot M k xs k=xs := by simp [slot]
 theorem slot_update (k : M.K) (xs ys : List Bool) : update (slot M k xs) k ys=slot M k ys := by
  funext j
  by_cases h : j=k <;> simp [slot,h]

 theorem store_update_local (s : M.K → List Bool) (xs ys : List Bool) (k : M.K) (w : List Bool) :
    update (store M s xs ys) (.inl k) w=store M (update s k w) xs ys := by
  funext j
  rcases j with j | j
  · simp [store,update_apply]
  · cases j <;> simp [store]
 theorem store_update_source (s : M.K → List Bool) (xs ys w : List Bool) :
    update (store M s xs ys) (source M) w=store M s w ys := by
  funext j
  rcases j with j | j <;> try cases j
  all_goals simp [store]
 theorem store_update_buffer (s : M.K → List Bool) (xs ys w : List Bool) :
    update (store M s xs ys) (buffer M) w=store M s xs w := by
  funext j
  rcases j with j | j <;> try cases j
  all_goals simp [store]

def body (tail : List Bool) : Embedding M.K M.Label M.State (Key M) (Label M) (State M) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := store M s tail []
  stack_key _ _ := rfl
  stack_update s k x := (store_update_local M s tail [] k x).symm
  label := Sum.inl
  halted := some (emitting M)
  stop := .goto (fun _ => emitting M)
  stop_spec _ _ := rfl

 theorem body_stmt (tail : List Bool) (s : TM2.Stmt (fun _ : M.K => Bool) M.Label M.State) :
    (body M tail).stmt s=(body M []).stmt s := by
  induction s <;> simp_all [Embedding.stmt,body]

def clean (v : State M) : State M := (v.1,none)

def readCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (source M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.getD false)
      (.pop (source M) (fun v b => (v.1,b))
        (.push (buffer M) (fun v => v.2.getD false)
          (.load (clean M) (.goto (fun _ => reading M)))))
      (.load (clean M) (.goto (fun _ => loading M))))

def loadCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (buffer M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (.inl M.input) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => loading M))))
      (.load (clean M) (.goto (fun _ => .inl M.main))))

def emitCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (.inl M.output) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (buffer M) (fun _ => true) (.push (buffer M) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => emitting M)))))
      (.push (buffer M) (fun _ => false)
        (.load (clean M) (.goto (fun _ => draining M)))))

def drainCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (buffer M) (fun v b => (v.1,b))
    (.branch (fun v => v.2.isSome)
      (.push (source M) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => draining M))))
      (.load (clean M) .halt))

def code : Label M → TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M)
  | .inl l => (body M []).stmt (M.code l)
  | .inr i => if i=0 then readCode M else if i=1 then loadCode M else if i=2 then emitCode M else drainCode M

abbrev machine : Machine where
  K := Key M
  input := source M
  output := source M
  Label := Label M
  main := reading M
  State := State M
  initial := (M.initial,none)
  code := code M

 theorem code_body (tail : List Bool) (l : M.Label) :
    (machine M).code ((body M tail).label l)=(body M tail).stmt (M.code l) := (body_stmt M tail _).symm

def readCfg (xs tail buf : List Bool) : (machine M).Cfg :=
  ⟨some (reading M),(M.initial,none),store M (fun _ => []) (quote xs++tail) buf⟩

def loadCfg (tail buf xs : List Bool) : (machine M).Cfg :=
  ⟨some (loading M),(M.initial,none),store M (slot M M.input xs) tail buf⟩

def emitCfg (tail xs buf : List Bool) : (machine M).Cfg :=
  ⟨some (emitting M),(M.initial,none),store M (slot M M.output xs) tail buf⟩

def drainCfg (tail buf : List Bool) : (machine M).Cfg :=
  ⟨some (draining M),(M.initial,none),store M (fun _ => []) tail buf⟩

 theorem read_cons (b : Bool) (xs tail buf : List Bool) :
    (machine M).step (readCfg M (b::xs) tail buf)=some (readCfg M xs tail (b::buf)) := by
  simp [readCfg,TM2.step,code,readCode,TM2.stepAux,quote,clean,
    store_update_source,store_update_buffer]

 theorem read_nil (tail buf : List Bool) :
    (machine M).step (readCfg M [] tail buf)=some (loadCfg M tail buf []) := by
  simp [readCfg,loadCfg,TM2.step,code,readCode,TM2.stepAux,quote,clean,
    store_update_source,slot_nil]

 theorem read_run (xs tail buf : List Bool) :
    Trace (machine M).step (xs.length+1) (readCfg M xs tail buf) (loadCfg M tail (xs.reverse++buf) []) := by
  induction xs generalizing buf with
  | nil => exact Trace.cons (read_nil M tail buf) (Trace.refl _)
  | cons b xs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (read_cons M b xs tail buf) (ih (b::buf))

 theorem load_cons (b : Bool) (tail buf xs : List Bool) :
    (machine M).step (loadCfg M tail (b::buf) xs)=some (loadCfg M tail buf (b::xs)) := by
  simp [loadCfg,TM2.step,code,loadCode,TM2.stepAux,clean,
    store_update_buffer,store_update_local,slot_update,slot_self]

 theorem load_nil (tail xs : List Bool) :
    (machine M).step (loadCfg M tail [] xs)=some ((body M tail).cfg (M.initialCfg xs)) := by
  simp [loadCfg,Embedding.cfg,body,Machine.initialCfg,TM2.step,code,loadCode,TM2.stepAux,
    clean,store_update_buffer,slot]
  rfl

 theorem load_run (tail buf xs : List Bool) :
    Trace (machine M).step (buf.length+1) (loadCfg M tail buf xs)
      ((body M tail).cfg (M.initialCfg (buf.reverse++xs))) := by
  induction buf generalizing xs with
  | nil => exact Trace.cons (load_nil M tail xs) (Trace.refl _)
  | cons b bs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (load_cons M b tail bs xs) (ih (b::xs))

 theorem emit_cons (b : Bool) (tail xs buf : List Bool) :
    (machine M).step (emitCfg M tail (b::xs) buf)=some (emitCfg M tail xs (b::true::buf)) := by
  simp [emitCfg,TM2.step,code,emitCode,TM2.stepAux,clean,
    store_update_local,store_update_buffer,slot_update,slot_self]

 theorem emit_nil (tail buf : List Bool) :
    (machine M).step (emitCfg M tail [] buf)=some (drainCfg M tail (false::buf)) := by
  simp [emitCfg,drainCfg,TM2.step,code,emitCode,TM2.stepAux,clean,
    store_update_local,store_update_buffer,slot_nil]

 theorem emit_run (tail xs buf : List Bool) :
    Trace (machine M).step (xs.length+1) (emitCfg M tail xs buf)
      (drainCfg M tail ((quote xs).reverse++buf)) := by
  induction xs generalizing buf with
  | nil => exact Trace.cons (emit_nil M tail buf) (Trace.refl _)
  | cons b xs ih =>
      simpa only [List.length_cons,quote,List.reverse_cons,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using
        Trace.cons (emit_cons M b tail xs buf) (ih (b::true::buf))

 theorem drain_cons (b : Bool) (tail buf : List Bool) :
    (machine M).step (drainCfg M tail (b::buf))=some (drainCfg M (b::tail) buf) := by
  simp [drainCfg,TM2.step,code,drainCode,TM2.stepAux,clean,
    store_update_source,store_update_buffer]

 theorem drain_nil (tail : List Bool) :
    (machine M).step (drainCfg M tail [])=some ((machine M).finalCfg tail) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    rcases k with k | k <;> try cases k
    all_goals simp [Machine.finalCfg,code,drainCode,TM2.stepAux,clean]

 theorem drain_run (tail buf : List Bool) :
    Trace (machine M).step (buf.length+1) (drainCfg M tail buf) ((machine M).finalCfg (buf.reverse++tail)) := by
  induction buf generalizing tail with
  | nil => exact Trace.cons (drain_nil M tail) (Trace.refl _)
  | cons b bs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (drain_cons M b tail bs) (ih (b::tail))

 theorem body_final (tail xs : List Bool) : (body M tail).cfg (M.finalCfg xs)=emitCfg M tail xs [] := rfl

 theorem run {xs zs : List Bool} {n : ℕ} (tail : List Bool)
    (h : Trace M.step n (M.initialCfg xs) (M.finalCfg zs)) :
    Trace (machine M).step (2*xs.length+3*zs.length+5+n)
      ((machine M).initialCfg (quote xs++tail)) ((machine M).finalCfg (quote zs++tail)) := by
  have hi : (machine M).initialCfg (quote xs++tail)=readCfg M xs tail [] := by
    apply cfg_ext <;> try rfl
    funext k
    rcases k with k | k <;> try cases k
    all_goals simp [Machine.initialCfg,readCfg,store]
  rw [hi]
  have ha := read_run M xs tail []
  simp only [List.append_nil] at ha
  have hb := load_run M tail xs.reverse []
  simp only [List.reverse_reverse,List.append_nil,List.length_reverse] at hb
  have hc := (body M tail).trace M.code (machine M).code (code_body M tail) h
  rw [body_final] at hc
  have hd := emit_run M tail zs []
  simp only [List.append_nil] at hd
  have he := drain_run M tail (quote zs).reverse
  simp only [List.reverse_reverse,List.length_reverse,quote_length] at he
  have hx := (((ha.trans hb).trans hc).trans hd).trans he
  convert hx using 1
  omega

end Thread

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {f : α → β}

 noncomputable def thread (P : PolyProgram ea eb f) (ec : γ → List Bool) :
    PolyProgram (encodePair ea ec) (encodePair eb ec) (fun x => (f x.1,x.2)) where
  machine := Thread.machine P.machine
  time := 2*X+3*P.sizeBound+5+P.time
  outputs x := by
    have hp := P.outputs x.1
    have h := Thread.run P.machine (ec x.2) (Trace.of_iterate hp.evals_in_steps)
    refine ⟨⟨_,h.iterate_eq⟩,?_⟩
    have hn : (ea x.1).length≤(encodePair ea ec x).length := by simp only [encodePair_length]; omega
    have hl := (P.length_bound x.1).trans (polynomial_eval_mono P.sizeBound hn)
    have ht := hp.steps_le_m.trans (polynomial_eval_mono P.time hn)
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
    omega

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanParallelTransducer -/
section
namespace OAI


                                                 
section
namespace MetricKMedian.Binary
open Turing Function Polynomial Finset

structure ParallelTransducer where
  Q : Type
  [finiteQ : Fintype Q]
  initial : Q
  next : Q → Bool → Q × (List Bool × List Bool)
  finish : Q → List Bool × List Bool
attribute [instance] ParallelTransducer.finiteQ

namespace ParallelTransducer
variable (T : ParallelTransducer)

def run : T.Q → List Bool → List Bool × List Bool
  | q, [] => T.finish q
  | q, b::xs =>
    let v := T.next q b
    let z := run v.1 xs
    (v.2.1++z.1,v.2.2++z.2)

def width : ℕ := max (univ.sup (fun q => (T.finish q).1.length+(T.finish q).2.length))
  (univ.sup (fun x : T.Q × Bool => (T.next x.1 x.2).2.1.length+(T.next x.1 x.2).2.2.length))

 theorem finish_length (q : T.Q) : (T.finish q).1.length+(T.finish q).2.length≤T.width :=
  (le_sup (f:=fun q => (T.finish q).1.length+(T.finish q).2.length) (mem_univ q)).trans (Nat.le_max_left _ _)

 theorem next_length (q : T.Q) (b : Bool) :
    (T.next q b).2.1.length+(T.next q b).2.2.length≤T.width :=
  (le_sup (f:=fun x : T.Q × Bool => (T.next x.1 x.2).2.1.length+(T.next x.1 x.2).2.2.length)
    (mem_univ (q,b))).trans (Nat.le_max_right _ _)

 theorem run_length (q : T.Q) (xs : List Bool) :
    (T.run q xs).1.length+(T.run q xs).2.length≤T.width*(xs.length+1) := by
  induction xs generalizing q with
  | nil => simpa only [run,List.length_nil,zero_add,mul_one] using T.finish_length q
  | cons b xs ih =>
      have hn := T.next_length q b
      have ht := ih (T.next q b).1
      simp only [run,List.length_append,List.length_cons]
      rw [show xs.length+1+1=(xs.length+1)+1 by rfl,Nat.mul_add,mul_one]
      omega

abbrev Key := Fin 4
abbrev input : Key := 0
abbrev left : Key := 1
abbrev right : Key := 2
abbrev output : Key := 3
abbrev Label := T.Q ⊕ Bool
abbrev State := Option Bool

def store (xs ls rs ys : List Bool) : Key → List Bool :=
  fun k => if k=input then xs else if k=left then ls else if k=right then rs else ys

 theorem store_update_input (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) input zs=store zs ls rs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_left (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) left zs=store xs zs rs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_right (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) right zs=store xs ls zs ys := by
  funext k
  fin_cases k <;> simp [store,input,left,right]
 theorem store_update_output (xs ls rs ys zs : List Bool) :
    update (store xs ls rs ys) output zs=store xs ls rs zs := by
  funext k
  fin_cases k <;> simp [store,input,left,right,output]

def emit (k : Key) : List Bool → TM2.Stmt (fun _ : Key => Bool) (Label T) State →
    TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | [], s => s
  | b::bs, s => .push k (fun _ => b) (emit k bs s)

 theorem emit_step (k : Key) (bits : List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (stk : Key → List Bool) :
    TM2.stepAux (emit T k bits s) v stk=TM2.stepAux s v (update stk k (bits.reverse++stk k)) := by
  induction bits generalizing stk with
  | nil => simp only [emit,List.reverse_nil,List.nil_append,update_eq_self]
  | cons b bs ih =>
      simp only [emit,TM2.stepAux,ih,update_self,update_idem,List.reverse_cons,
        List.append_assoc,List.singleton_append]

def emitPair (p : List Bool × List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State) :=
  emit T left p.1 (emit T right p.2 s)

 theorem emitPair_step (p : List Bool × List Bool) (s : TM2.Stmt (fun _ : Key => Bool) (Label T) State)
    (v : State) (xs ls rs ys : List Bool) :
    TM2.stepAux (emitPair T p s) v (store xs ls rs ys)=
      TM2.stepAux s v (store xs (p.1.reverse++ls) (p.2.reverse++rs) ys) := by
  simp [emitPair,emit_step,store,input,left,right,store_update_left,store_update_right]

def transfer (phase : Bool) : TM2.Stmt (fun _ : Key => Bool) (Label T) State :=
  .pop (if phase then left else right) (fun _ b => b)
    (.branch Option.isSome
      (.push output (fun b => b.getD false) (.load (fun _ => none) (.goto (fun _ => .inr phase))))
      (.load (fun _ => none) (if phase then .halt else .goto (fun _ => .inr true))))

def code : Label T → TM2.Stmt (fun _ : Key => Bool) (Label T) State
  | .inl q => .pop input (fun _ b => b)
      (.branch Option.isSome
        (.branch (fun b => b.getD false)
          (.load (fun _ => none) (emitPair T (T.next q true).2 (.goto (fun _ => .inl (T.next q true).1))))
          (.load (fun _ => none) (emitPair T (T.next q false).2 (.goto (fun _ => .inl (T.next q false).1)))))
        (.load (fun _ => none) (emitPair T (T.finish q) (.goto (fun _ => .inr false)))))
  | .inr b => transfer T b

abbrev machine : Machine where
  K := Key
  input := input
  output := output
  Label := Label T
  main := .inl T.initial
  State := State
  initial := none
  code := code T

def readCfg (q : T.Q) (xs ls rs : List Bool) : (machine T).Cfg :=
  ⟨some (.inl q),none,store xs ls rs []⟩
def rightCfg (ls rs ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inr false),none,store [] ls rs ys⟩
def leftCfg (ls ys : List Bool) : (machine T).Cfg :=
  ⟨some (.inr true),none,store [] ls [] ys⟩

 theorem read_cons (q : T.Q) (b : Bool) (xs ls rs : List Bool) :
    (machine T).step (T.readCfg q (b::xs) ls rs)=
      some (T.readCfg (T.next q b).1 xs ((T.next q b).2.1.reverse++ls) ((T.next q b).2.2.reverse++rs)) := by
  cases b <;> simp [readCfg,TM2.step,code,TM2.stepAux,store,input,emitPair_step,store_update_input]

 theorem read_nil (q : T.Q) (ls rs : List Bool) :
    (machine T).step (T.readCfg q [] ls rs)=
      some (T.rightCfg ((T.finish q).1.reverse++ls) ((T.finish q).2.reverse++rs) []) := by
  simp [readCfg,rightCfg,TM2.step,code,TM2.stepAux,store,input,emitPair_step,store_update_input]

 theorem read_run (q : T.Q) (xs ls rs : List Bool) :
    Trace (machine T).step (xs.length+1) (T.readCfg q xs ls rs)
      (T.rightCfg ((T.run q xs).1.reverse++ls) ((T.run q xs).2.reverse++rs) []) := by
  induction xs generalizing q ls rs with
  | nil => exact Trace.cons (T.read_nil q ls rs) (Trace.refl _)
  | cons b xs ih =>
      simpa only [run,List.length_cons,List.reverse_append,List.append_assoc] using
        Trace.cons (T.read_cons q b xs ls rs)
          (ih (T.next q b).1 ((T.next q b).2.1.reverse++ls) ((T.next q b).2.2.reverse++rs))

 theorem right_cons (b : Bool) (ls rs ys : List Bool) :
    (machine T).step (T.rightCfg ls (b::rs) ys)=some (T.rightCfg ls rs (b::ys)) := by
  simp [rightCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_right,store_update_output]

 theorem right_nil (ls ys : List Bool) :
    (machine T).step (T.rightCfg ls [] ys)=some (T.leftCfg ls ys) := by
  simp [rightCfg,leftCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_right]

 theorem right_run (ls rs ys : List Bool) :
    Trace (machine T).step (rs.length+1) (T.rightCfg ls rs ys) (T.leftCfg ls (rs.reverse++ys)) := by
  induction rs generalizing ys with
  | nil => exact Trace.cons (T.right_nil ls ys) (Trace.refl _)
  | cons b rs ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (T.right_cons b ls rs ys) (ih (b::ys))

 theorem left_cons (b : Bool) (ls ys : List Bool) :
    (machine T).step (T.leftCfg (b::ls) ys)=some (T.leftCfg ls (b::ys)) := by
  simp [leftCfg,TM2.step,code,transfer,TM2.stepAux,store,input,left,right,output,store_update_left,store_update_output]

 theorem left_nil (ys : List Bool) :
    (machine T).step (T.leftCfg [] ys)=some ((machine T).finalCfg ys) := by
  apply congrArg some
  apply cfg_ext
  · rfl
  · rfl
  · funext k
    fin_cases k <;> simp [Machine.finalCfg,code,transfer,TM2.stepAux,store,input,left,right,output]

 theorem left_run (ls ys : List Bool) :
    Trace (machine T).step (ls.length+1) (T.leftCfg ls ys) ((machine T).finalCfg (ls.reverse++ys)) := by
  induction ls generalizing ys with
  | nil => exact Trace.cons (T.left_nil ys) (Trace.refl _)
  | cons b ls ih =>
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using
        Trace.cons (T.left_cons b ls ys) (ih (b::ys))

 theorem run_trace (xs : List Bool) :
    Trace (machine T).step (xs.length+(T.run T.initial xs).1.length+(T.run T.initial xs).2.length+3)
      ((machine T).initialCfg xs)
      ((machine T).finalCfg ((T.run T.initial xs).1++(T.run T.initial xs).2)) := by
  have hi : (machine T).initialCfg xs=T.readCfg T.initial xs [] [] := by
    apply cfg_ext <;> try rfl
    funext k
    fin_cases k <;> simp [Machine.initialCfg,readCfg,store,input,left,right]
  rw [hi]
  have hr := T.read_run T.initial xs [] []
  simp only [List.append_nil] at hr
  have hs := T.right_run (T.run T.initial xs).1.reverse (T.run T.initial xs).2.reverse []
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at hs
  have ht := T.left_run (T.run T.initial xs).1.reverse (T.run T.initial xs).2
  simp only [List.length_reverse,List.reverse_reverse] at ht
  have h := (hr.trans hs).trans ht
  convert h using 1
  omega

noncomputable def program : PolyProgram id id (fun xs => (T.run T.initial xs).1++(T.run T.initial xs).2) where
  machine := machine T
  time := C (T.width+1)*X+C (T.width+3)
  outputs xs := by
    refine ⟨⟨_,(T.run_trace xs).iterate_eq⟩,?_⟩
    have hl := T.run_length T.initial xs
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,id_eq]
    nlinarith

end ParallelTransducer
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanProducts -/
section
namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace WordTransducer

def identity : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[b])
  finish _ := []

 theorem identity_run (xs : List Bool) : identity.run () xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::identity.run () xs=b::xs; rw [ih]

def constant (s : List Bool) : Transducer where
  Q := Unit
  initial := ()
  next _ _ := ((),[])
  finish _ := s

 theorem constant_run (s xs : List Bool) : (constant s).run () xs=s := by
  induction xs with
  | nil => rfl
  | cons b xs ih => exact ih

def duplicate : ParallelTransducer where
  Q := Unit
  initial := ()
  next _ b := ((),([true,b],[b]))
  finish _ := ([false],[])

 theorem duplicate_run (xs : List Bool) : duplicate.run () xs=(quote xs,xs) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change (true::b::(duplicate.run () xs).1,b::(duplicate.run () xs).2)=_
      rw [ih]
      rfl

def exchange : ParallelTransducer where
  Q := Option Bool
  initial := none
  next q b := match q with
    | none => (some (!b),([],[]))
    | some false => (none,([],[b]))
    | some true => (some true,([true,b],[]))
  finish _ := ([false],[])

 theorem exchange_done (xs : List Bool) : exchange.run (some true) xs=(quote xs,[]) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change (true::b::(exchange.run (some true) xs).1,(exchange.run (some true) xs).2)=_
      rw [ih]
      rfl

 theorem exchange_run (xs ys : List Bool) : exchange.run none (quote xs++ys)=(quote ys,xs) := by
  induction xs with
  | nil => exact exchange_done ys
  | cons b xs ih =>
      change ((exchange.run none (quote xs++ys)).1,b::(exchange.run none (quote xs++ys)).2)=_
      rw [ih]

end WordTransducer

namespace PolyProgram
variable {α β γ δ : Type}
variable {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool} {ed : δ → List Bool}
variable {f : α → β} {g : γ → δ}

noncomputable def identity (ea : α → List Bool) : PolyProgram ea ea _root_.id :=
  WordTransducer.identity.program.of_word (fun a => by
    simpa only [WordTransducer.identity,id_eq] using WordTransducer.identity_run (ea a))

noncomputable def constant (ea : α → List Bool) (eb : β → List Bool) (b : β) :
    PolyProgram ea eb (fun _ => b) :=
  (WordTransducer.constant (eb b)).program.of_word (fun a => by
    simpa only [WordTransducer.constant] using WordTransducer.constant_run (eb b) (ea a))

noncomputable def duplicate (ea : α → List Bool) : PolyProgram ea (encodePair ea ea) (fun a => (a,a)) :=
  WordTransducer.duplicate.program.of_word (fun a => by
    have h := congrArg (fun p : List Bool × List Bool => p.1++p.2) (WordTransducer.duplicate_run (ea a))
    simpa only [WordTransducer.duplicate,encodePair] using h)

noncomputable def exchange (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram (encodePair ea eb) (encodePair eb ea) Prod.swap :=
  WordTransducer.exchange.program.of_word (fun x => by
    have h := congrArg (fun p : List Bool × List Bool => p.1++p.2) (WordTransducer.exchange_run (ea x.1) (eb x.2))
    simpa only [WordTransducer.exchange,encodePair,Prod.swap] using h)

noncomputable def second (P : PolyProgram ea eb f) (ec : γ → List Bool) :
    PolyProgram (encodePair ec ea) (encodePair ec eb) (fun x => (x.1,f x.2)) :=
  (((exchange ec ea).comp (P.thread ec)).comp (exchange eb ec)).congr _ (fun _ => rfl)

noncomputable def product (P : PolyProgram ea eb f) (Q : PolyProgram ec ed g) :
    PolyProgram (encodePair ea ec) (encodePair eb ed) (fun x => (f x.1,g x.2)) :=
  ((P.thread ec).comp (Q.second eb)).congr _ (fun _ => rfl)

noncomputable def fanout {h : α → γ} (P : PolyProgram ea eb f) (Q : PolyProgram ea ec h) :
    PolyProgram ea (encodePair eb ec) (fun a => (f a,h a)) :=
  ((duplicate ea).comp (P.product Q)).congr _ (fun _ => rfl)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanLoop -/
section
namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

namespace Loop
variable (M : Machine)
abbrev Key := M.K ⊕ Unit
abbrev Label := M.Label ⊕ Option Bool
abbrev State := M.State × Option Bool
abbrev auxiliary : Key M := .inr ()
abbrev check : Label M := .inr none
abbrev phase (b : Bool) : Label M := .inr (some b)

def body : Embedding M.K M.Label M.State (Key M) (Label M) (State M) where
  key := Sum.inl
  read := Prod.fst
  write v x := (x,v.2)
  state v := (v,none)
  read_state _ := rfl
  write_state _ _ := rfl
  stack s := Sum.elim s (fun _ => [])
  stack_key _ _ := rfl
  stack_update s k x := by
    funext j
    rcases j with j | j <;>
      simp only [update_apply,Sum.elim_inl,Sum.elim_inr,Sum.inl.injEq,Sum.inr_ne_inl,ite_false]
  label := Sum.inl
  halted := some (check M)
  stop := .goto (fun _ => check M)
  stop_spec _ _ := rfl

def source (b : Bool) : Key M := if b then auxiliary M else .inl M.output

def target (b : Bool) : Key M := if b then .inl M.input else auxiliary M

 theorem source_ne_target (b : Bool) : source M b ≠ target M b := by
  cases b <;> simp [source,target,auxiliary]

def following (b : Bool) : Label M := if b then .inl M.main else phase M true

def clean (v : State M) : State M := (v.1,none)

def transfer (b : Bool) : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (source M b) (fun v c => (v.1,c))
    (.branch (fun v => v.2.isSome)
      (.push (target M b) (fun v => v.2.getD false)
        (.load (clean M) (.goto (fun _ => phase M b))))
      (.load (clean M) (.goto (fun _ => following M b))))

def checkCode : TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M) :=
  .pop (.inl M.output) (fun v c => (v.1,c))
    (.branch (fun v => v.2.getD false)
      (.load (clean M) (.goto (fun _ => phase M false)))
      (.load (clean M) .halt))

def code : Label M → TM2.Stmt (fun _ : Key M => Bool) (Label M) (State M)
  | .inl l => (body M).stmt (M.code l)
  | .inr none => checkCode M
  | .inr (some b) => transfer M b

abbrev machine : Machine where
  K := Key M
  input := .inl M.input
  output := .inl M.output
  Label := Label M
  main := .inl M.main
  State := State M
  initial := (M.initial,none)
  code := code M

 theorem code_body (l : M.Label) : (machine M).code ((body M).label l)=
    (body M).stmt (M.code l) := rfl

 theorem initial_body (s : List Bool) : (body M).cfg (M.initialCfg s)=
    (machine M).initialCfg s := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Embedding.cfg,body,Machine.initialCfg]

def transferCfg (b : Bool) (xs ys : List Bool) : (machine M).Cfg :=
  ⟨some (phase M b),(M.initial,none),twoStacks (source M b) (target M b) xs ys⟩

 theorem transfer_cons (b x : Bool) (xs ys : List Bool) :
    (machine M).step (transferCfg M b (x::xs) ys)=some (transferCfg M b xs (x::ys)) := by
  change some (TM2.stepAux (transfer M b) (M.initial,none)
    (twoStacks (source M b) (target M b) (x::xs) ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_cons,List.tail_cons,Option.isSome_some,Bool.cond_true,Option.getD_some,clean]
  rw [update_of_ne (Ne.symm (source_ne_target M b)),twoStacks_target (source_ne_target M b)]
  rw [twoStacks_move (source_ne_target M b)]
  rfl

 theorem transfer_run (b : Bool) (xs ys : List Bool) :
    Trace (machine M).step xs.length (transferCfg M b xs ys)
      (transferCfg M b [] (xs.reverse++ys)) := by
  induction xs generalizing ys with
  | nil => exact Trace.refl _
  | cons x xs ih =>
      have h := Trace.cons (transfer_cons M b x xs ys) (ih (x::ys))
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using h

 theorem transfer_empty (b : Bool) (ys : List Bool) :
    (machine M).step (transferCfg M b [] ys)=
      some ⟨some (following M b),(M.initial,none),twoStacks (source M b) (target M b) [] ys⟩ := by
  change some (TM2.stepAux (transfer M b) (M.initial,none)
    (twoStacks (source M b) (target M b) [] ys))=_
  simp only [transfer,TM2.stepAux]
  rw [twoStacks_source]
  simp only [List.head?_nil,List.tail_nil,Option.isSome_none,Bool.cond_false,clean,twoStacks_pop_empty]

 theorem transfer_change (ys : List Bool) :
    (machine M).step (transferCfg M false [] ys)=some (transferCfg M true ys []) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [transferCfg,source,target,twoStacks,auxiliary]

 theorem transfer_end (ys : List Bool) :
    (machine M).step (transferCfg M true [] ys)=some ((machine M).initialCfg ys) := by
  rw [transfer_empty]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [Machine.initialCfg,source,target,twoStacks,auxiliary]

 theorem transfer_full (xs : List Bool) :
    Trace (machine M).step (2*xs.length+2) (transferCfg M false xs []) ((machine M).initialCfg xs) := by
  have h₁ := transfer_run M false xs []
  simp only [List.append_nil] at h₁
  have h₂ := Trace.cons (transfer_change M xs.reverse) (transfer_run M true xs.reverse [])
  simp only [List.length_reverse,List.reverse_reverse,List.append_nil] at h₂
  have h₃ := Trace.cons (transfer_end M xs) (Trace.refl _)
  have hh := (h₁.trans h₂).trans h₃
  simpa only [show xs.length+(xs.length+1)+(0+1)=2*xs.length+2 by omega] using hh

def checkCfg (xs : List Bool) : (machine M).Cfg :=
  ⟨some (check M),(M.initial,none),fun k => if k=Sum.inl M.output then xs else []⟩

 theorem body_final (xs : List Bool) : (body M).cfg (M.finalCfg xs)=checkCfg M xs := by
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [body,Embedding.cfg,Machine.finalCfg,checkCfg]

 theorem check_step (b : Bool) (xs : List Bool) :
    (machine M).step (checkCfg M (b::xs))=
      some ⟨if b then some (phase M false) else none,(M.initial,none),
        fun k => if k=Sum.inl M.output then xs else []⟩ := by
  change some (TM2.stepAux (checkCode M) (M.initial,none)
    (fun k => if k=Sum.inl M.output then b::xs else []))=_
  simp only [checkCode,TM2.stepAux,List.head?_cons,List.tail_cons,
    Option.getD_some,clean,ite_true]
  cases b <;> simp only [Bool.cond_false,Bool.cond_true,Bool.false_eq_true,ite_false,ite_true]
  all_goals
    apply congrArg some
    apply cfg_ext <;> try rfl
    funext k
    by_cases h : k=Sum.inl M.output <;> simp [h]

 theorem check_false (xs : List Bool) :
    (machine M).step ((body M).cfg (M.finalCfg (false::xs)))=some ((machine M).finalCfg xs) := by
  rw [body_final,check_step]
  rfl

 theorem check_true (xs : List Bool) :
    (machine M).step ((body M).cfg (M.finalCfg (true::xs)))=some (transferCfg M false xs []) := by
  rw [body_final,check_step]
  apply congrArg some
  apply cfg_ext <;> try rfl
  funext k
  rcases k with k | k <;> simp [transferCfg,twoStacks,source,target,auxiliary]

 theorem stop {s t : List Bool} {n : ℕ}
    (hM : Trace M.step n (M.initialCfg s) (M.finalCfg (false::t))) :
    Trace (machine M).step (n+1) ((machine M).initialCfg s) ((machine M).finalCfg t) := by
  have h := (body M).trace M.code (machine M).code (code_body M) hM
  rw [initial_body] at h
  exact h.trans (Trace.cons (check_false M t) (Trace.refl _))

 theorem next {s t u : List Bool} {n m : ℕ}
    (hM : Trace M.step n (M.initialCfg s) (M.finalCfg (true::t)))
    (hR : Trace (machine M).step m ((machine M).initialCfg t) ((machine M).finalCfg u)) :
    Trace (machine M).step (n+2*t.length+3+m) ((machine M).initialCfg s) ((machine M).finalCfg u) := by
  have h := (body M).trace M.code (machine M).code (code_body M) hM
  rw [initial_body] at h
  have hg := Trace.cons (check_true M t) (transfer_full M t)
  have hh := (h.trans hg).trans hR
  simpa only [Nat.add_assoc,show 2*t.length+2+1=2*t.length+3 by omega] using hh

end Loop

def encodeLoop {α β : Type} (ea : α → List Bool) (eb : β → List Bool) : β ⊕ α → List Bool
  | .inl b => false::eb b
  | .inr a => true::ea a

inductive BoundedRun {α β : Type} (ea : α → List Bool) (f : α → β ⊕ α) (S : ℕ) :
    ℕ → α → β → Prop
  | stop {a b} : (ea a).length ≤ S → f a=.inl b → BoundedRun ea f S 1 a b
  | step {a a' b n} : (ea a).length ≤ S → f a=.inr a' →
      BoundedRun ea f S n a' b → BoundedRun ea f S (n+1) a b

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {f : α → β ⊕ α}

noncomputable def passTime (P : PolyProgram ea (encodeLoop ea eb) f) (S : ℕ) : ℕ :=
  P.time.eval S+2*P.sizeBound.eval S+3

 theorem run_loop (P : PolyProgram ea (encodeLoop ea eb) f) {S n : ℕ} {a : α} {b : β}
    (h : BoundedRun ea f S n a b) :
    ∃ t ≤ n*P.passTime S, Trace (Loop.machine P.machine).step t
      ((Loop.machine P.machine).initialCfg (ea a)) ((Loop.machine P.machine).finalCfg (eb b)) := by
  induction h with
  | @stop a b ha hab =>
      have hp := P.outputs a
      have ht : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
          (P.machine.finalCfg (false::eb b)) := by
        have hh : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
            (P.machine.finalCfg (encodeLoop ea eb (f a))) := Trace.of_iterate hp.evals_in_steps
        simpa only [hab,encodeLoop] using hh
      refine ⟨hp.steps+1,?_,Loop.stop P.machine ht⟩
      have htime := hp.steps_le_m.trans (polynomial_eval_mono P.time ha)
      simp only [passTime,one_mul]
      omega
  | @step a a' b n ha haa' h ih =>
      obtain ⟨t,ht,htrace⟩ := ih
      have hp := P.outputs a
      have hb : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
          (P.machine.finalCfg (true::ea a')) := by
        have hh : Trace P.machine.step hp.steps (P.machine.initialCfg (ea a))
            (P.machine.finalCfg (encodeLoop ea eb (f a))) := Trace.of_iterate hp.evals_in_steps
        simpa only [haa',encodeLoop] using hh
      refine ⟨hp.steps+2*(ea a').length+3+t,?_,Loop.next P.machine hb htrace⟩
      have htime := hp.steps_le_m.trans (polynomial_eval_mono P.time ha)
      have hl := (P.length_bound a).trans (polynomial_eval_mono P.sizeBound ha)
      simp only [haa',encodeLoop,List.length_cons] at hl
      dsimp only [passTime] at ht ⊢
      rw [Nat.add_mul]
      omega

noncomputable def loop (P : PolyProgram ea (encodeLoop ea eb) f) (g : α → β)
    (iterations sizes : Polynomial ℕ)
    (h : ∀ a, ∃ n ≤ iterations.eval (ea a).length,
      BoundedRun ea f (sizes.eval (ea a).length) n a (g a)) : PolyProgram ea eb g where
  machine := Loop.machine P.machine
  time := iterations*(P.time.comp sizes+2*P.sizeBound.comp sizes+3)
  outputs a := Classical.choice (show Nonempty _ from by
    obtain ⟨n,hn,hrun⟩ := h a
    obtain ⟨t,ht,htrace⟩ := P.run_loop hrun
    refine ⟨⟨⟨t,htrace.iterate_eq⟩,?_⟩⟩
    refine ht.trans ?_
    simpa only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_comp,
      Polynomial.eval_ofNat,passTime] using Nat.mul_le_mul_right (P.passTime (sizes.eval (ea a).length)) hn)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanListPrimitives -/
section
namespace OAI


                                             
section
namespace MetricKMedian.Binary
open Turing Function Polynomial

def encodeBool (b : Bool) : List Bool := [b]

namespace WordTransducer

def emptyTest : Transducer where
  Q := Bool
  initial := true
  next _ _ := (false,[])
  finish b := [b]

 theorem emptyTest_run (q : Bool) (xs : List Bool) :
    emptyTest.run q xs=[q && xs.isEmpty] := by
  induction xs generalizing q with
  | nil => cases q <;> rfl
  | cons b xs ih =>
      change emptyTest.run false xs=_
      rw [ih]
      simp

def head : Transducer where
  Q := Option Bool
  initial := none
  next q b := (q.or (some b),[])
  finish q := [q.getD false]

 theorem head_run (q : Option Bool) (xs : List Bool) :
    head.run q xs=[(q.or xs.head?).getD false] := by
  induction xs generalizing q with
  | nil => cases q <;> rfl
  | cons b xs ih =>
      change head.run (q.or (some b)) xs=_
      rw [ih]
      cases q <;> rfl

def tail : Transducer where
  Q := Bool
  initial := true
  next q b := (false,if q then [] else [b])
  finish _ := []

 theorem tail_run_false (xs : List Bool) : tail.run false xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::tail.run false xs=b::xs; rw [ih]

 theorem tail_run (xs : List Bool) : tail.run true xs=xs.tail := by
  cases xs with
  | nil => rfl
  | cons b xs => exact tail_run_false xs

abbrev prepend : Transducer where
  Q := Fin 4
  initial := 0
  next q b := if q=0 then (1,[]) else if q=1 then (2,[b]) else if q=2 then (3,[]) else (3,[b])
  finish _ := []

 theorem prepend_done (xs : List Bool) : prepend.run 3 xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change b::prepend.run 3 xs=b::xs
      rw [ih]

 theorem prepend_run (b : Bool) (xs : List Bool) :
    prepend.run 0 (quote [b]++xs)=b::xs := by
  change b::prepend.run 3 xs=b::xs
  rw [prepend_done]

def prependWord (p : List Bool) : Transducer where
  Q := Bool
  initial := true
  next q b := (false,if q then p++[b] else [b])
  finish q := if q then p else []

 theorem prefix_done (p xs : List Bool) : (prependWord p).run false xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::(prependWord p).run false xs=b::xs; rw [ih]

 theorem prefix_run (p xs : List Bool) : (prependWord p).run true xs=p++xs := by
  cases xs with
  | nil => exact (List.append_nil p).symm
  | cons b xs =>
      change (p++[b])++(prependWord p).run false xs=p++b::xs
      rw [prefix_done,List.append_assoc,List.singleton_append]

def select : Transducer where
  Q := Fin 2 ⊕ (Bool × Option (Option Bool))
  initial := .inl 0
  next q b := match q with
    | .inl k => if k=0 then (.inl 1,[]) else (.inr (b,none),[])
    | .inr (keep,none) => (.inr (keep,some none),[])
    | .inr (keep,some none) => (.inr (keep,some (some (!b))),[])
    | .inr (keep,some (some false)) => (.inr (keep,some none),if keep then [] else [b])
    | .inr (keep,some (some true)) => (.inr (keep,some (some true)),if keep then [b] else [])
  finish _ := []

 theorem select_done (keep : Bool) (xs : List Bool) :
    select.run (.inr (keep,some (some true))) xs=if keep then xs else [] := by
  induction xs with
  | nil => cases keep <;> rfl
  | cons b xs ih =>
      change (if keep then [b] else [])++select.run (.inr (keep,some (some true))) xs=_
      rw [ih]
      cases keep <;> simp

 theorem select_pair (keep : Bool) (xs ys : List Bool) :
    select.run (.inr (keep,some none)) (quote xs++ys)=if keep then ys else xs := by
  induction xs with
  | nil => exact select_done keep ys
  | cons b xs ih =>
      change (if keep then [] else [b])++select.run (.inr (keep,some none)) (quote xs++ys)=_
      rw [ih]
      cases keep <;> simp

 theorem select_run (keep : Bool) (xs ys : List Bool) :
    select.run (.inl 0) (quote [keep]++quote xs++ys)=if keep then ys else xs := by
  exact select_pair keep xs ys

end WordTransducer

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool}

noncomputable def isEmpty : PolyProgram id encodeBool List.isEmpty :=
  WordTransducer.emptyTest.program.of_word (fun xs => by
    simpa only [WordTransducer.emptyTest,Bool.true_and,encodeBool,id_eq] using WordTransducer.emptyTest_run true xs)

noncomputable def head : PolyProgram id encodeBool (fun xs => xs.head?.getD false) :=
  WordTransducer.head.program.of_word (fun xs => by
    simpa only [WordTransducer.head,Option.or,encodeBool,id_eq] using WordTransducer.head_run none xs)

noncomputable def tail : PolyProgram id id List.tail :=
  WordTransducer.tail.program.of_word (fun xs => by
    simpa only [WordTransducer.tail,id_eq] using WordTransducer.tail_run xs)

noncomputable def cons : PolyProgram (encodePair encodeBool id) id (fun x => x.1::x.2) :=
  WordTransducer.prepend.program.of_word (fun x => by
    simpa only [WordTransducer.prepend,encodePair,encodeBool,id_eq] using WordTransducer.prepend_run x.1 x.2)

noncomputable def prependWord (p : List Bool) : PolyProgram id id (fun xs => p++xs) :=
  (WordTransducer.prependWord p).program.of_word (fun xs => by
    simpa only [WordTransducer.prependWord,id_eq] using WordTransducer.prefix_run p xs)

noncomputable def injectLeft (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram eb (encodeLoop ea eb) Sum.inl :=
  (prependWord [false]).of_word (fun _ => rfl)

noncomputable def injectRight (ea : α → List Bool) (eb : β → List Bool) :
    PolyProgram ea (encodeLoop ea eb) Sum.inr :=
  (prependWord [true]).of_word (fun _ => rfl)

noncomputable def select (eb : β → List Bool) :
    PolyProgram (encodePair encodeBool (encodePair eb eb)) eb
      (fun x => if x.1 then x.2.2 else x.2.1) :=
  WordTransducer.select.program.of_word (fun x => by
    simpa only [WordTransducer.select,encodePair,encodeBool,List.append_assoc,apply_ite] using
      WordTransducer.select_run x.1 (eb x.2.1) (eb x.2.2))

noncomputable def ite {p : α → Bool} {f g : α → β}
    (P : PolyProgram ea encodeBool p) (F : PolyProgram ea eb f) (G : PolyProgram ea eb g) :
    PolyProgram ea eb (fun a => if p a then g a else f a) :=
  ((P.fanout (F.fanout G)).comp (select eb)).congr _ (fun _ => rfl)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanRecode -/
section
namespace OAI


                                     
section
namespace MetricKMedian.Binary.PolyProgram
variable {α β α' β' : Type} {ea : α → List Bool} {eb : β → List Bool}
variable {ea' : α' → List Bool} {eb' : β' → List Bool} {f : α → β} {f' : α' → β'}

def recode (P : PolyProgram ea eb f) (i : α' → α)
    (hi : ∀ a, ea (i a)=ea' a) (ho : ∀ a, eb (f (i a))=eb' (f' a)) :
    PolyProgram ea' eb' f' where
  machine := P.machine
  time := P.time
  outputs a := by
    have h := P.outputs (i a)
    rwa [hi,ho] at h

end MetricKMedian.Binary.PolyProgram
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryLists -/
section
namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Function Polynomial

 def encodeList {α : Type} (ea : α → List Bool) : List α → List Bool
  | [] => []
  | a::as => quote (ea a)++encodeList ea as

namespace EncodedList
variable {α : Type} (ea : α → List Bool)
 theorem nil : encodeList ea []=[] := rfl
 theorem cons (a : α) (as : List α) : encodeList ea (a::as)=quote (ea a)++encodeList ea as := rfl
 theorem cons_length (a : α) (as : List α) : (encodeList ea (a::as)).length=2*(ea a).length+1+(encodeList ea as).length := by
  simp only [encodeList,List.length_append,quote_length]
 theorem length_le (as : List α) : as.length ≤ (encodeList ea as).length := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [cons_length,List.length_cons]; omega
 theorem isEmpty (as : List α) : (encodeList ea as).isEmpty=as.isEmpty := by
  cases as with
  | nil => rfl
  | cons a as =>
      have h := cons_length ea a as
      apply List.isEmpty_eq_false_iff.mpr
      intro hz
      simp only [hz,List.length_nil] at h
      omega
 theorem append (as bs : List α) : encodeList ea (as++bs)=encodeList ea as++encodeList ea bs := by
  induction as with
  | nil => rfl
  | cons a as ih => simp only [List.cons_append,encodeList,ih,List.append_assoc]
 theorem reverse_length (as : List α) : (encodeList ea as.reverse).length=(encodeList ea as).length := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.reverse_cons,append,List.length_append,cons_length,nil,List.length_nil,ih]
      omega
 theorem member_length (as : List α) (a : α) (h : a∈as) : (ea a).length ≤ (encodeList ea as).length := by
  induction as with
  | nil => simp at h
  | cons b as ih =>
      simp only [List.mem_cons] at h
      rcases h with rfl|h
      · rw [cons_length]; omega
      · have hh := ih h
        rw [cons_length]; omega
 theorem length_bound (as : List α) (L : ℕ) (h : ∀ a∈as, (ea a).length ≤ L) :
    (encodeList ea as).length ≤ as.length*(2*L+1) := by
  induction as with
  | nil => simp only [nil,List.length_nil,zero_mul,le_refl]
  | cons a as ih =>
      have ha := h a (by simp)
      have hh := ih (fun a ha => h a (by simp [ha]))
      rw [cons_length,List.length_cons]
      nlinarith
end EncodedList

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listIsEmpty : PolyProgram (encodeList ea) encodeBool List.isEmpty :=
  isEmpty.recode (encodeList ea) (fun _ => rfl) (fun as => by rw [EncodedList.isEmpty])

noncomputable def listUncons : PolyProgram (encodeList ea) (encodePair ea (encodeList ea))
    (fun as => (as.head?.getD a0,as.tail)) := by
  let raw : PolyProgram (encodeList ea) id (encodeList ea) := (identity id).recode (encodeList ea) (fun _ => rfl) (fun _ => rfl)
  let deflt := constant (encodeList ea) id (Binary.quote (ea a0))
  refine (ite (listIsEmpty ea) raw deflt).recode id (fun _ => rfl) ?_
  intro as
  cases as with
  | nil => simp [encodePair,encodeList]
  | cons a as => rfl
noncomputable def listHead : PolyProgram (encodeList ea) ea (fun as => as.head?.getD a0) :=
  ((listUncons ea a0).comp (fst ea (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listTail : PolyProgram (encodeList ea) (encodeList ea) List.tail :=
  ((listUncons ea a0).comp (snd ea (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listCons : PolyProgram (encodePair ea (encodeList ea)) (encodeList ea) (fun x => x.1::x.2) :=
  (identity id).recode (encodePair ea (encodeList ea)) (fun _ => rfl) (fun _ => rfl)
end PolyProgram

namespace ListReverse
variable {α : Type} (ea : α → List Bool) (a0 : α)
abbrev enc : List α × List α → List Bool := encodePair (encodeList ea) (encodeList ea)
 def body (s : List α × List α) : List α ⊕ (List α × List α) :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,s.1.head?.getD a0::s.2)
 def result (s : List α × List α) : List α := s.1.reverse++s.2

noncomputable def program : PolyProgram (enc ea) (encodeLoop (enc ea) (encodeList ea)) (body a0) := by
  let px := PolyProgram.fst (encodeList ea) (encodeList ea)
  let py := PolyProgram.snd (encodeList ea) (encodeList ea)
  let hd := px.comp (PolyProgram.listHead ea a0)
  let tl := px.comp (PolyProgram.listTail ea a0)
  let newLast := (hd.fanout py).comp (PolyProgram.listCons ea)
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight (enc ea) (encodeList ea))
  let done := py.comp (PolyProgram.injectLeft (enc ea) (encodeList ea))
  exact (PolyProgram.ite (px.comp (PolyProgram.listIsEmpty ea)) recur done).congr _ (fun _ => rfl)

 theorem run (as bs : List α) (S : ℕ) (h : 2*(encodeList ea as).length+1+(encodeList ea bs).length ≤ S) :
    BoundedRun (enc ea) (body a0) S (as.length+1) (as,bs) (as.reverse++bs) := by
  induction as generalizing bs with
  | nil =>
      apply BoundedRun.stop
      · simpa only [enc,encodePair_length] using h
      · rfl
  | cons a as ih =>
      have hs : 2*(encodeList ea as).length+1+(encodeList ea (a::bs)).length ≤ S := by
        simp only [EncodedList.cons_length] at h ⊢
        omega
      have hr := BoundedRun.step (ea:=enc ea) (f:=body a0)
        (a:=(a::as,bs)) (a':=(as,a::bs))
        (by simpa only [enc,encodePair_length] using h) rfl (ih (a::bs) hs)
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hr

noncomputable def loop : PolyProgram (enc ea) (encodeList ea) result :=
  (program ea a0).loop result (X+1) X (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · have h := EncodedList.length_le ea s.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]; omega
    · simpa only [eval_X,enc,encodePair_length,result] using run ea a0 s.1 s.2
        (2*(encodeList ea s.1).length+1+(encodeList ea s.2).length) le_rfl)
end ListReverse

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listReverse : PolyProgram (encodeList ea) (encodeList ea) List.reverse :=
  (((identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList ea) [])).comp (ListReverse.loop ea a0)).congr _
    (fun _ => List.append_nil _)
noncomputable def listAppend : PolyProgram (encodePair (encodeList ea) (encodeList ea)) (encodeList ea) (fun x => x.1++x.2) :=
  (((listReverse ea a0).thread (encodeList ea)).comp (ListReverse.loop ea a0)).congr _
    (fun _ => by simp only [Function.comp_apply,ListReverse.result,List.reverse_reverse])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListFold -/
section
namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ListFold
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α)
variable (op : β × α → β)
abbrev enc : List α × β → List Bool := encodePair (encodeList ea) eb
 def body (s : List α × β) : β ⊕ (List α × β) :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,op (s.2,s.1.head?.getD a0))
 def result (s : List α × β) : β := s.1.foldl (fun b a => op (b,a)) s.2

noncomputable def program (P : PolyProgram (encodePair eb ea) eb op) :
    PolyProgram (enc ea eb) (encodeLoop (enc ea eb) eb) (body a0 op) := by
  let px := PolyProgram.fst (encodeList ea) eb
  let py := PolyProgram.snd (encodeList ea) eb
  let hd := px.comp (PolyProgram.listHead ea a0)
  let tl := px.comp (PolyProgram.listTail ea a0)
  let newLast := (py.fanout hd).comp P
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight (enc ea eb) eb)
  let done := py.comp (PolyProgram.injectLeft (enc ea eb) eb)
  exact (PolyProgram.ite (px.comp (PolyProgram.listIsEmpty ea)) recur done).congr _ (fun _ => rfl)

 theorem run (as : List α) (b : β) (S : ℕ)
    (h : ∀ pre suf, as=pre++suf → (enc ea eb (suf,pre.foldl (fun b a => op (b,a)) b)).length ≤ S) :
    BoundedRun (enc ea eb) (body a0 op) S (as.length+1) (as,b) (result op (as,b)) := by
  induction as generalizing b with
  | nil =>
      apply BoundedRun.stop
      · exact h [] [] rfl
      · rfl
  | cons a as ih =>
      have hs : ∀ pre suf, as=pre++suf →
          (enc ea eb (suf,pre.foldl (fun b a => op (b,a)) (op (b,a)))).length ≤ S := by
        intro pre suf he
        exact h (a::pre) suf (by simp only [List.cons_append,he])
      exact BoundedRun.step (h [] (a::as) rfl) rfl (ih (op (b,a)) hs)

noncomputable def loop (P : PolyProgram (encodePair eb ea) eb op) (B : Polynomial ℕ)
    (hB : ∀ (as : List α) (b : β) pre suf, as=pre++suf →
      (eb (pre.foldl (fun b a => op (b,a)) b)).length ≤ B.eval (enc ea eb (as,b)).length) :
    PolyProgram (enc ea eb) eb (result op) :=
  (program ea eb a0 op P).loop (result op) (X+1) (2*X+1+B) (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · have h := EncodedList.length_le ea s.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]; omega
    · apply run
      intro pre suf he
      have hh := hB s.1 s.2 pre suf he
      have hx : (encodeList ea suf).length ≤ (encodeList ea s.1).length := by
        rw [he,EncodedList.append,List.length_append]
        omega
      simp only [enc,encodePair_length] at hh ⊢
      simp only [eval_add,eval_mul,eval_ofNat,eval_X,eval_one]
      omega)

 theorem linear_height (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1))
    (as : List α) (b : β) :
    (eb (as.foldl (fun b a => op (b,a)) b)).length ≤ (eb b).length+C*(encodeList ea as).length := by
  induction as generalizing b with
  | nil => simp only [List.foldl_nil,EncodedList.nil,List.length_nil,mul_zero,add_zero,le_refl]
  | cons a as ih =>
      have hh := ih (op (b,a))
      have ha := hop b a
      simp only [List.foldl_cons,EncodedList.cons_length]
      nlinarith

noncomputable def linearLoop (P : PolyProgram (encodePair eb ea) eb op) (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1)) :
    PolyProgram (enc ea eb) eb (result op) :=
  loop ea eb a0 op P ((Polynomial.C C+1)*X) (fun as b pre suf he => by
    have hh := linear_height ea eb op C hop pre b
    have hp : (encodeList ea pre).length ≤ (encodeList ea as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    simp only [eval_mul,eval_add,eval_C,eval_one,eval_X,enc,encodePair_length]
    nlinarith)
end ListFold

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {op : β × α → β}
noncomputable def listFold (P : PolyProgram (encodePair eb ea) eb op) (a0 : α) (B : Polynomial ℕ)
    (hB : ∀ (as : List α) (b : β) pre suf, as=pre++suf →
      (eb (pre.foldl (fun b a => op (b,a)) b)).length ≤ B.eval (encodePair (encodeList ea) eb (as,b)).length) :
    PolyProgram (encodePair (encodeList ea) eb) eb (fun x => x.1.foldl (fun b a => op (b,a)) x.2) :=
  ListFold.loop ea eb a0 op P B hB
noncomputable def listFoldLinear (P : PolyProgram (encodePair eb ea) eb op) (a0 : α) (C : ℕ)
    (hop : ∀ b a, (eb (op (b,a))).length ≤ (eb b).length+C*(2*(ea a).length+1)) :
    PolyProgram (encodePair (encodeList ea) eb) eb (fun x => x.1.foldl (fun b a => op (b,a)) x.2) :=
  ListFold.linearLoop ea eb a0 op P C hop
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanFinite -/
section
namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Finset

namespace FiniteTransducer
variable {α β : Type} [Fintype α] (ea : α → List Bool) (eb : β → List Bool) (f : α → β)

noncomputable def prefixes : Finset (List Bool) :=
  univ.biUnion (fun a => (ea a).inits.toFinset)

 theorem mem_prefixes (a : α) (xs ys : List Bool) (h : xs++ys=ea a) : xs∈prefixes ea := by
  classical
  apply mem_biUnion.mpr
  refine ⟨a,mem_univ _,List.mem_toFinset.mpr ?_⟩
  exact (List.mem_inits _ _).mpr ⟨ys,h⟩

abbrev Q := Option {xs : List Bool // xs∈prefixes ea}

noncomputable def state (xs : List Bool) : Q ea :=
  if h : xs∈prefixes ea then some ⟨xs,h⟩ else none

noncomputable abbrev table : Transducer where
  Q := Q ea
  initial := state ea []
  next q b := (match q with | none => none | some xs => state ea (xs.val++[b]),[])
  finish q := match q with
    | none => []
    | some xs => if h : ∃ a, ea a=xs.val then eb (f (Classical.choose h)) else []

 theorem next_state (xs : List Bool) (b : Bool) (h : xs∈prefixes ea) :
    (table ea eb f).next (state ea xs) b=(state ea (xs++[b]),[]) := by
  simp only [table,state,dif_pos h]

 theorem finish_state (a : α) (hinj : Injective ea) :
    (table ea eb f).finish (state ea (ea a))=eb (f a) := by
  have hm := mem_prefixes ea a (ea a) [] (List.append_nil _)
  have hex : ∃ a', ea a'=ea a := ⟨a,rfl⟩
  simp only [state,dif_pos hm,dif_pos hex]
  have he := Classical.choose_spec hex
  rw [hinj he]

 theorem run_state (a : α) (hinj : Injective ea) (xs ys : List Bool) (h : xs++ys=ea a) :
    (table ea eb f).run (state ea xs) ys=eb (f a) := by
  induction ys generalizing xs with
  | nil =>
      have he : xs=ea a := by simpa only [List.append_nil] using h
      rw [he]
      exact finish_state ea eb f a hinj
  | cons b ys ih =>
      change ((table ea eb f).next (state ea xs) b).2 ++
        (table ea eb f).run ((table ea eb f).next (state ea xs) b).1 ys = _
      rw [next_state ea eb f xs b (mem_prefixes ea a xs (b::ys) h),List.nil_append]
      apply ih
      simpa only [List.append_assoc,List.singleton_append] using h

noncomputable def program (hinj : Injective ea) : PolyProgram ea eb f :=
  (table ea eb f).program.of_word (fun a =>
    run_state ea eb f a hinj [] (ea a) rfl)

end FiniteTransducer

 theorem encodeBool_injective : Injective encodeBool := by
  intro a b h
  simpa only [encodeBool,List.cons.injEq,true_and,and_true] using h

 theorem quote_injective : Injective quote := by
  intro xs ys h
  have hh := congrArg ((WordTransducer.projecting false).run none) h
  have hx := WordTransducer.projecting_pair false xs []
  have hy := WordTransducer.projecting_pair false ys []
  simp only [List.append_nil,Bool.false_eq_true,ite_false] at hx hy
  rwa [hx,hy] at hh

 theorem encodePair_injective {α β : Type} {ea : α → List Bool} {eb : β → List Bool}
    (ha : Injective ea) (hb : Injective eb) : Injective (encodePair ea eb) := by
  intro a b h
  have hx := congrArg ((WordTransducer.projecting false).run none) h
  have hy := congrArg ((WordTransducer.projecting true).run none) h
  simp only [encodePair,WordTransducer.projecting_pair,Bool.false_eq_true,ite_false,ite_true] at hx hy
  exact Prod.ext (ha hx) (hb hy)

namespace PolyProgram

noncomputable def boolFunction {α β : Type} [Fintype α] (ea : α → List Bool) (eb : β → List Bool)
    (f : α → β) (hinj : Injective ea) : PolyProgram ea eb f :=
  FiniteTransducer.program ea eb f hinj

noncomputable def boolNot : PolyProgram encodeBool encodeBool Bool.not :=
  boolFunction _ _ _ encodeBool_injective
noncomputable def boolAnd : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => x.1 && x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)
noncomputable def boolOr : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => x.1 || x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BooleanReverse -/
section
namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ReverseLoop
abbrev S := List Bool × List Bool
abbrev enc : S → List Bool := encodePair id id

def body (s : S) : List Bool ⊕ S :=
  if s.1.isEmpty then .inl s.2 else .inr (s.1.tail,s.1.head?.getD false::s.2)

def result (s : S) : List Bool := s.1.reverse++s.2

noncomputable def program : PolyProgram enc (encodeLoop enc id) body := by
  let first := PolyProgram.fst id id
  let last := PolyProgram.snd id id
  let hd := first.comp PolyProgram.head
  let tl := first.comp PolyProgram.tail
  let newLast := (hd.fanout last).comp PolyProgram.cons
  let recur := (tl.fanout newLast).comp (PolyProgram.injectRight enc id)
  let done := last.comp (PolyProgram.injectLeft enc id)
  exact (PolyProgram.ite (first.comp PolyProgram.isEmpty) recur done).congr _ (fun _ => rfl)

 theorem run (xs ys : List Bool) (S : ℕ) (h : 2*xs.length+1+ys.length≤S) :
    BoundedRun enc body S (xs.length+1) (xs,ys) (xs.reverse++ys) := by
  induction xs generalizing ys with
  | nil =>
      apply BoundedRun.stop
      · simpa only [enc,encodePair_length,id_eq,List.length_nil,zero_mul,zero_add] using h
      · rfl
  | cons b xs ih =>
      have hs : 2*xs.length+1+(b::ys).length≤S := by simp only [List.length_cons] at h ⊢; omega
      have hr := BoundedRun.step (ea:=enc) (f:=body)
        (a:=(b::xs,ys)) (a':=(xs,b::ys))
        (by simpa only [enc,encodePair_length,id_eq] using h) rfl (ih (b::ys) hs)
      simpa only [List.length_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using hr

noncomputable def loop : PolyProgram enc id result :=
  program.loop result (X+1) X (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc,encodePair_length,id_eq]; omega
    · simpa only [eval_X,enc,encodePair_length,id_eq,result] using run s.1 s.2 (2*s.1.length+1+s.2.length) le_rfl)

end ReverseLoop

namespace PolyProgram
noncomputable def reverse : PolyProgram id id List.reverse :=
  (((identity id).fanout (constant id id [])).comp ReverseLoop.loop).congr _
    (fun _ => List.append_nil _)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryWords -/
section
namespace OAI


                                   
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word

def value : List Bool → ℕ
  | [] => 0
  | b::bs => b.toNat+2*value bs

@[simp] theorem value_nil : value []=0 := rfl
@[simp] theorem value_cons (b : Bool) (xs : List Bool) : value (b::xs)=b.toNat+2*value xs := rfl

 theorem value_bits (n : ℕ) : value n.bits=n := by
  induction n using Nat.binaryRec' with
  | zero => rfl
  | bit b n hn ih => rw [Nat.bits_append_bit n b hn,value_cons,ih,Nat.bit_val]; omega

 theorem value_zero (xs : List Bool) : value xs=0 ↔ ∀ b∈xs,b=false := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp only [value_cons,Nat.add_eq_zero_iff,Nat.mul_eq_zero,OfNat.ofNat_ne_zero,false_or,Bool.toNat_eq_zero,ih,List.forall_mem_cons]

 theorem bits_value (xs : List Bool) (h : xs.getLast?≠some false) : (value xs).bits=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      by_cases he : xs=[]
      · subst xs
        cases b
        · exact False.elim (h rfl)
        · rfl
      · have ht : xs.getLast?≠some false := by
          intro hh
          apply h
          simp only [List.getLast?_cons,hh,Option.getD_some]
        rw [value_cons,show b.toNat+2*value xs=Nat.bit b (value xs) by rw [Nat.bit_val]; omega]
        rw [Nat.bits_append_bit,ih ht]
        intro hzero
        exfalso
        have hh := value_zero xs |>.mp hzero
        have hl := List.getLast_mem he
        have hb := hh _ hl
        apply ht
        rw [List.getLast?_eq_some_getLast he,hb]

 theorem value_append (xs ys : List Bool) : value (xs++ys)=value xs+2^xs.length*value ys := by
  induction xs with
  | nil => simp
  | cons b xs ih => simp only [List.cons_append,value_cons,ih,List.length_cons,pow_succ]; ring

 theorem value_reverse_drop (xs : List Bool) : value (xs.dropWhile Bool.not).reverse=value xs.reverse := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b
      · simp only [List.dropWhile_cons,Bool.not_false,ite_true,List.reverse_cons,value_append,
          value_cons,value_nil,Bool.toNat_false,Nat.mul_zero,Nat.add_zero,zero_add]
        exact ih
      · simp

 theorem drop_head (xs : List Bool) : (xs.dropWhile Bool.not).head?≠some false := by
  induction xs with
  | nil => simp
  | cons b xs ih => cases b <;> simp_all

 def normalize (xs : List Bool) : List Bool := (xs.reverse.dropWhile Bool.not).reverse

 theorem normalize_eq_bits (xs : List Bool) : normalize xs=(value xs).bits := by
  have hv : value (normalize xs)=value xs := by
    simpa only [normalize,List.reverse_reverse] using value_reverse_drop xs.reverse
  rw [← hv,bits_value]
  simp only [normalize,List.getLast?_reverse]
  exact drop_head _

end Word

namespace WordTransducer

def dropFalse : Transducer where
  Q := Bool
  initial := false
  next q b := (q || b,if q || b then [b] else [])
  finish _ := []

 theorem dropFalse_true (xs : List Bool) : dropFalse.run true xs=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => change b::dropFalse.run true xs=b::xs; rw [ih]

 theorem dropFalse_run (xs : List Bool) : dropFalse.run false xs=xs.dropWhile Bool.not := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      cases b
      · exact ih
      · exact congrArg (List.cons true) (dropFalse_true xs)

end WordTransducer

namespace PolyProgram
noncomputable def append : PolyProgram (encodePair id id) id (fun x : List Bool × List Bool => x.1++x.2) :=
  ((reverse.thread id).comp ReverseLoop.loop).congr _ (fun x => by
    simp only [Function.comp_apply,ReverseLoop.result,List.reverse_reverse])

noncomputable def dropFalse : PolyProgram id id (List.dropWhile Bool.not) :=
  WordTransducer.dropFalse.program.of_word (fun xs => by
    simpa only [WordTransducer.dropFalse,id_eq] using WordTransducer.dropFalse_run xs)

noncomputable def normalize : PolyProgram id id Word.normalize :=
  ((reverse.comp dropFalse).comp reverse).congr _ (fun _ => rfl)

noncomputable def toBits : PolyProgram id Nat.bits Word.value :=
  normalize.of_word (fun xs => Word.normalize_eq_bits xs)

end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryAddition -/
section
namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word

def sumBit (a b c : Bool) : Bool := xor (xor a b) c
 def carryBit (a b c : Bool) : Bool := (a && b) || (a && c) || (b && c)

 theorem fullAdder (a b c : Bool) :
    (sumBit a b c).toNat+2*(carryBit a b c).toNat=a.toNat+b.toNat+c.toNat := by
  cases a <;> cases b <;> cases c <;> decide

 def add : List Bool → List Bool → Bool → List Bool
  | [],[],c => if c then [true] else []
  | a::xs,ys,c => sumBit a (ys.head?.getD false) c :: add xs ys.tail (carryBit a (ys.head?.getD false) c)
  | [],b::ys,c => sumBit false b c :: add [] ys (carryBit false b c)
termination_by xs ys _ => xs.length+ys.length

 theorem add_step (xs ys : List Bool) (c : Bool) (h : (xs.isEmpty && ys.isEmpty)=false) :
    add xs ys c=sumBit (xs.head?.getD false) (ys.head?.getD false) c ::
      add xs.tail ys.tail (carryBit (xs.head?.getD false) (ys.head?.getD false) c) := by
  cases xs <;> cases ys <;> simp_all only [List.isEmpty_nil,List.isEmpty_cons,Bool.true_and,Bool.false_and,
    Bool.true_eq_false,List.head?_cons,List.head?_nil,Option.getD_some,Option.getD_none,
    List.tail_nil,List.tail_cons,add]

 theorem value_add (xs ys : List Bool) (c : Bool) : value (add xs ys c)=value xs+value ys+c.toNat := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => cases c <;> simp [add,value]
      | cons b ys ih =>
          rw [add,value_cons,ih]
          have h := fullAdder false b c
          simp only [value_nil,value_cons,Bool.toNat_false] at *
          omega
  | cons a xs ih =>
      rw [add,value_cons,ih]
      have h := fullAdder a (ys.head?.getD false) c
      cases ys with
      | nil => simp only [List.head?_nil,Option.getD_none,List.tail_nil,value_nil,value_cons,Bool.toNat_false] at *; omega
      | cons b ys => simp only [List.head?_cons,Option.getD_some,List.tail_cons,value_cons] at *; omega

end Word

namespace AdditionLoop
abbrev S := List Bool × (List Bool × (Bool × List Bool))
abbrev ec : Bool × List Bool → List Bool := encodePair encodeBool id
abbrev ey : List Bool × (Bool × List Bool) → List Bool := encodePair id ec
abbrev enc : S → List Bool := encodePair id ey
 def empty (s : S) : Bool := s.1.isEmpty && s.2.1.isEmpty
 def next (s : S) : S :=
  (s.1.tail,(s.2.1.tail,(Word.carryBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1,
    Word.sumBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1 :: s.2.2.2)))
 def finish (s : S) : List Bool := (if s.2.2.1 then true::s.2.2.2 else s.2.2.2).reverse
 def body (s : S) : List Bool ⊕ S := if empty s then .inl (finish s) else .inr (next s)
 def result (s : S) : List Bool := s.2.2.2.reverse++Word.add s.1 s.2.1 s.2.2.1

 theorem enc_length (s : S) : (enc s).length=2*s.1.length+2*s.2.1.length+s.2.2.2.length+5 := by
  simp only [enc,ey,ec,encodePair_length,encodeBool,id_eq,List.length_cons,List.length_nil]
  omega

noncomputable def program : PolyProgram enc (encodeLoop enc id) body := by
  let px := PolyProgram.fst id ey
  let pyz := PolyProgram.snd id ey
  let py := pyz.comp (PolyProgram.fst id ec)
  let pca := pyz.comp (PolyProgram.snd id ec)
  let pc := pca.comp (PolyProgram.fst encodeBool id)
  let pa := pca.comp (PolyProgram.snd encodeBool id)
  let bits := (px.comp PolyProgram.head).fanout ((py.comp PolyProgram.head).fanout pc)
  let binj := encodePair_injective encodeBool_injective (encodePair_injective encodeBool_injective encodeBool_injective)
  let sb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.sumBit v.1 v.2.1 v.2.2) binj)
  let cb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.carryBit v.1 v.2.1 v.2.2) binj)
  let na := (sb.fanout pa).comp PolyProgram.cons
  let pn := (px.comp PolyProgram.tail).fanout ((py.comp PolyProgram.tail).fanout (cb.fanout na))
  let pe := ((px.comp PolyProgram.isEmpty).fanout (py.comp PolyProgram.isEmpty)).comp PolyProgram.boolAnd
  let pf := (PolyProgram.ite pc pa ((PolyProgram.constant enc encodeBool true).fanout pa |>.comp PolyProgram.cons)).comp PolyProgram.reverse
  exact (PolyProgram.ite pe (pn.comp (PolyProgram.injectRight enc id))
    (pf.comp (PolyProgram.injectLeft enc id))).congr _ (fun _ => rfl)

 theorem shorten (s : S) (h : empty s=false) :
    s.1.tail.length+s.2.1.tail.length<s.1.length+s.2.1.length := by
  rcases s with ⟨xs,ys,c,acc⟩
  cases xs <;> cases ys <;> simp_all [empty]
  omega

 theorem next_result (s : S) (h : empty s=false) : result (next s)=result s := by
  simp only [result]
  rw [Word.add_step s.1 s.2.1 s.2.2.1 h]
  simp only [next,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem next_size (s : S) (h : empty s=false) : (enc (next s)).length≤(enc s).length := by
  have hs := shorten s h
  simp only [enc_length,next,List.length_cons]
  omega

 theorem run (L : ℕ) : ∀ (s : S) (S : ℕ), s.1.length+s.2.1.length=L → (enc s).length≤S →
    ∃ n≤L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL hs
      cases he : empty s with
      | true =>
          refine ⟨1,by omega,BoundedRun.stop hs ?_⟩
          rcases s with ⟨xs,ys,c,acc⟩
          have hz : xs=[] ∧ ys=[] := by simpa only [empty,Bool.and_eq_true,List.isEmpty_iff] using he
          rcases hz with ⟨rfl,rfl⟩
          cases c <;> simp [body,empty,finish,result,Word.add]
      | false =>
          have hl : (next s).1.length+(next s).2.1.length<L := by simpa only [next,hL] using shorten s he
          obtain ⟨n,hn,hr⟩ := ih _ hl (next s) S rfl ((next_size s he).trans hs)
          refine ⟨n+1,by omega,?_⟩
          rw [next_result s he] at hr
          exact BoundedRun.step hs (by simp only [body,he,Bool.false_eq_true,ite_false]) hr

noncomputable def loop : PolyProgram enc id result :=
  program.loop result (X+1) X (fun s => by
    obtain ⟨n,hn,hr⟩ := run (s.1.length+s.2.1.length) s (enc s).length rfl le_rfl
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc_length]; omega
    · simpa only [eval_X] using hr)

end AdditionLoop

namespace PolyProgram
noncomputable def addWords : PolyProgram (encodePair id id) id (fun x : List Bool × List Bool => Word.add x.1 x.2 false) := by
  let ex : List Bool × List Bool → List Bool := encodePair id id
  let init := (fst id id).fanout ((snd id id).fanout (constant ex AdditionLoop.ec (false,[])))
  exact (init.comp AdditionLoop.loop).congr _ (fun _ => rfl)

noncomputable def natAdd : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1+x.2) :=
  (addWords.comp toBits).recode (fun x => (x.1.bits,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.value_add,Word.value_bits,Bool.toNat_false,Nat.add_zero])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryNatural -/
section
namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word
 theorem normalize_length (xs : List Bool) : (normalize xs).length≤xs.length := by
  simpa only [normalize,List.length_reverse] using List.length_dropWhile_le Bool.not xs.reverse

 theorem bits_value_length (xs : List Bool) : (value xs).bits.length≤xs.length := by
  rw [← normalize_eq_bits]
  exact normalize_length xs
end Word

namespace NatBinary
 theorem zero_iff (n : ℕ) : n.bits=[] ↔ n=0 := by
  constructor
  · intro h
    have hv := Word.value_bits n
    rw [h,Word.value_nil] at hv
    exact hv.symm
  · rintro rfl; rfl

 theorem bit_length (b : Bool) (n : ℕ) : (Nat.bit b n).bits.length≤n.bits.length+1 := by
  have h := Word.bits_value_length (b::n.bits)
  simpa only [Word.value_cons,Word.value_bits,Nat.bit_val,Nat.add_comm,List.length_cons] using h

 theorem half_length (n : ℕ) : n.div2.bits.length=n.bits.length-1 := by
  rw [Nat.div2_bits_eq_tail,List.length_tail]

 theorem add_length (a b : ℕ) : (a+b).bits.length≤ max a.bits.length b.bits.length+1 := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have ha := (Nat.lt_size_self a).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (le_max_left a.size b.size))
  have hb := (Nat.lt_size_self b).trans_le (Nat.pow_le_pow_right (by decide : 1≤2) (le_max_right a.size b.size))
  rw [pow_succ]
  omega

 theorem mul_length (a b : ℕ) : (a*b).bits.length≤a.bits.length+b.bits.length := by
  simp only [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  rw [pow_add]
  nlinarith

 theorem length_mono {a b : ℕ} (h : a≤b) : a.bits.length≤b.bits.length := by
  simpa only [Nat.size_eq_bits_len] using Nat.size_le_size h

 theorem half_lt_length {n : ℕ} (hn : n≠0) : n.div2.bits.length<n.bits.length := by
  rw [half_length]
  have hh : n.bits≠[] := fun h => hn ((zero_iff n).mp h)
  have hl : 0<n.bits.length := List.length_pos_iff.mpr hh
  omega
end NatBinary

namespace PolyProgram
noncomputable def natBit : PolyProgram (encodePair encodeBool Nat.bits) Nat.bits (fun x : Bool × ℕ => Nat.bit x.1 x.2) :=
  (cons.comp toBits).recode (fun x => (x.1,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.value_cons,Word.value_bits,Nat.bit_val,Nat.add_comm])

noncomputable def natHalf : PolyProgram Nat.bits Nat.bits Nat.div2 :=
  tail.recode Nat.bits (fun _ => rfl) (fun n => (Nat.div2_bits_eq_tail n).symm)

noncomputable def natOdd : PolyProgram Nat.bits encodeBool Nat.bodd :=
  head.recode Nat.bits (fun _ => rfl) (fun n => by
    rw [Nat.bodd_eq_bits_head]
    cases n.bits <;> rfl)

noncomputable def natZero : PolyProgram Nat.bits encodeBool (fun n => decide (n=0)) :=
  isEmpty.recode Nat.bits (fun _ => rfl) (fun n => by
    congr 1
    cases h : n.bits.isEmpty
    · have hn : n≠0 := by intro hn; subst n; contradiction
      exact (decide_eq_false hn).symm
    · have hn : n=0 := (NatBinary.zero_iff n).mp (List.isEmpty_iff.mp h)
      exact (decide_eq_true hn).symm)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListMap -/
section
namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace ListAlgorithms
variable {α β : Type}
 theorem pushMap (f : α → β) (as : List α) (bs : List β) :
    as.foldl (fun bs a => f a::bs) bs=(as.map f).reverse++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      rw [List.foldl_cons,ih,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem pushFilter (f : α → Bool) (as bs : List α) :
    as.foldl (fun bs a => if f a then a::bs else bs) bs=(as.filter f).reverse++bs := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldl_cons,List.filter_cons]
      cases f a <;> simp only [Bool.false_eq_true,ite_false,ite_true,ih,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem count (as : List α) (n : ℕ) : as.foldl (fun n _ => n+1) n=n+as.length := by
  induction as generalizing n with
  | nil => rfl
  | cons a as ih => simp only [List.foldl_cons,ih,List.length_cons]; omega

 theorem all (p : α → Bool) (as : List α) (b : Bool) :
    as.foldl (fun b a => b && p a) b=(b && as.all p) := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.all_cons,Bool.and_assoc]

 theorem any (p : α → Bool) (as : List α) (b : Bool) :
    as.foldl (fun b a => b || p a) b=(b || as.any p) := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.any_cons,Bool.or_assoc]
end ListAlgorithms

namespace PolyProgram
variable {α β : Type} {ea : α → List Bool} {eb : β → List Bool} {f : α → β}
noncomputable def listMap (P : PolyProgram ea eb f) (a0 : α) :
    PolyProgram (encodeList ea) (encodeList eb) (List.map f) := by
  let step : PolyProgram (encodePair (encodeList eb) ea) (encodeList eb) (fun x => f x.2::x.1) :=
    (((P.second (encodeList eb)).comp (exchange (encodeList eb) eb)).comp (listCons eb)).congr _ (fun _ => rfl)
  let fold := step.listFold a0 (X*(2*P.sizeBound+1)+X) (by
    intro as bs pre suf he
    simp only [ListAlgorithms.pushMap,EncodedList.append,List.length_append,EncodedList.reverse_length]
    let L := (encodePair (encodeList ea) (encodeList eb) (as,bs)).length
    have hpre : (encodeList ea pre).length ≤ (encodeList ea as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    have hlen : pre.length ≤ L := by
      have hp := EncodedList.length_le ea pre
      simp only [L,encodePair_length]; omega
    have hbs : (encodeList eb bs).length ≤ L := by simp only [L,encodePair_length]; omega
    have hh := EncodedList.length_bound eb (pre.map f) (P.sizeBound.eval L) (by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      apply (P.length_bound a).trans
      apply polynomial_eval_mono
      have hmem := EncodedList.member_length ea pre a ha
      simp only [L,encodePair_length]; omega)
    simp only [List.length_map] at hh
    simp only [eval_add,eval_mul,eval_X,eval_ofNat,eval_one]
    change _ ≤ L*(2*P.sizeBound.eval L+1)+L
    nlinarith)
  let start := (identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList eb) [])
  exact ((start.comp fold).comp (listReverse eb (f a0))).congr _ (fun as => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.pushMap,List.append_nil,List.reverse_reverse])

noncomputable def listFilter {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) (encodeList ea) (List.filter p) := by
  let first := fst (encodeList ea) ea
  let test := (snd (encodeList ea) ea).comp P
  let push := (exchange (encodeList ea) ea).comp (listCons ea)
  let step : PolyProgram (encodePair (encodeList ea) ea) (encodeList ea) (fun x => if p x.2 then x.2::x.1 else x.1) :=
    (ite test first push).congr _ (fun _ => rfl)
  let fold := step.listFoldLinear a0 1 (by
    intro bs a
    simp only [one_mul]
    split_ifs
    · rw [EncodedList.cons_length]; omega
    · omega)
  exact ((((identity (encodeList ea)).fanout (constant (encodeList ea) (encodeList ea) [])).comp fold).comp (listReverse ea a0)).congr _
    (fun as => by simp only [Function.comp_apply,id_eq,ListAlgorithms.pushFilter,List.append_nil,List.reverse_reverse])

noncomputable def listLength (ea : α → List Bool) (a0 : α) :
    PolyProgram (encodeList ea) Nat.bits List.length := by
  let step : PolyProgram (encodePair Nat.bits ea) Nat.bits (fun x : ℕ × α => x.1+1) :=
    (((fst Nat.bits ea).fanout (constant (encodePair Nat.bits ea) Nat.bits 1)).comp natAdd).congr _ (fun _ => rfl)
  let fold := step.listFoldLinear a0 2 (by
    intro n a
    have h := NatBinary.add_length n 1
    have hone : (1:ℕ).bits.length=1 := rfl
    rw [hone] at h
    dsimp only
    omega)
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) Nat.bits 0)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Nat.zero_add] using ListAlgorithms.count as 0)

noncomputable def listAll {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) encodeBool (fun as => as.all p) := by
  let step := (P.second encodeBool).comp boolAnd
  let fold := step.listFoldLinear a0 0 (by intro b a; simp only [encodeBool,List.length_singleton,zero_mul,add_zero,le_refl])
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) encodeBool true)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Bool.true_and] using ListAlgorithms.all p as true)

noncomputable def listAny {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) encodeBool (fun as => as.any p) := by
  let step := (P.second encodeBool).comp boolOr
  let fold := step.listFoldLinear a0 0 (by intro b a; simp only [encodeBool,List.length_singleton,zero_mul,add_zero,le_refl])
  exact (((identity (encodeList ea)).fanout (constant (encodeList ea) encodeBool false)).comp fold).congr _
    (fun as => by simpa only [Function.comp_apply,id_eq,Bool.false_or] using ListAlgorithms.any p as false)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListContext -/
section
namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListAlgorithms
variable {α β γ : Type}
 theorem pushMapWith (f : γ × α → β) (as : List α) (c : γ) (bs : List β) :
    as.foldl (fun x a => (x.1,f (x.1,a)::x.2)) (c,bs)=(c,(as.map (fun a => f (c,a))).reverse++bs) := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih =>
      simpa only [List.foldl_cons,List.map_cons,List.reverse_cons,List.append_assoc,List.singleton_append] using ih (f (c,a)::bs)
 theorem pushMapWith_pair (f : γ × α → β) (as : List α) (x : γ × List β) :
    as.foldl (fun x a => (x.1,f (x.1,a)::x.2)) x=(x.1,(as.map (fun a => f (x.1,a))).reverse++x.2) := by
  cases x
  exact pushMapWith _ _ _ _
 theorem filterMapPair (p : γ × α → Bool) (c : γ) (as : List α) :
    (((as.map (fun a => (c,a))).filter p).map Prod.snd)=as.filter (fun a => p (c,a)) := by
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.map_cons,List.filter_cons]
      split <;> simp_all only [List.map_cons]
end ListAlgorithms

namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
noncomputable def listMapWith {f : γ × α → β}
    (P : PolyProgram (encodePair ec ea) eb f) (a0 : α) (b0 : β) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList eb) (fun x => x.2.map (fun a => f (x.1,a))) := by
  let eacc := encodePair ec (encodeList eb)
  let acc := fst eacc ea
  let c := acc.comp (fst ec (encodeList eb))
  let bs := acc.comp (snd ec (encodeList eb))
  let a := snd eacc ea
  let nb := ((c.fanout a).comp P).fanout bs
  let step : PolyProgram (encodePair eacc ea) eacc (fun x : (γ × List β) × α => (x.1.1,f (x.1.1,x.2)::x.1.2)) :=
    (c.fanout (nb.comp (listCons eb))).congr _ (fun _ => rfl)
  let B : Polynomial ℕ := 3*X+X*(2*P.sizeBound.comp (3*X+1)+1)+1
  let fold := step.listFold a0 B (by
    intro as x pre suf he
    let L := (encodePair (encodeList ea) eacc (as,x)).length
    have hc : (ec x.1).length ≤ L := by simp only [L,eacc,encodePair_length]; omega
    have hb : (encodeList eb x.2).length ≤ L := by simp only [L,eacc,encodePair_length]; omega
    have hp : (encodeList ea pre).length ≤ L := by
      have hh : (encodeList ea pre).length ≤ (encodeList ea as).length := by rw [he,EncodedList.append,List.length_append]; omega
      simp only [L,encodePair_length]; omega
    have hplen : pre.length ≤ L := (EncodedList.length_le ea pre).trans hp
    have hout := EncodedList.length_bound eb (pre.map (fun a => f (x.1,a))) (P.sizeBound.eval (3*L+1)) (by
      intro b hb
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
      apply (P.length_bound (x.1,a)).trans
      apply polynomial_eval_mono
      have hla := (EncodedList.member_length ea pre a ha).trans hp
      simp only [encodePair_length]
      omega)
    rw [List.length_map] at hout
    simp only [ListAlgorithms.pushMapWith_pair,eacc,encodePair_length,EncodedList.append,List.length_append,EncodedList.reverse_length]
    simp only [B,eval_add,eval_mul,eval_ofNat,eval_X,eval_one,eval_comp]
    simp only [L,eacc,encodePair_length] at hc hb hplen hout
    nlinarith)
  let start := (snd ec (encodeList ea)).fanout ((fst ec (encodeList ea)).fanout (constant (encodePair ec (encodeList ea)) (encodeList eb) []))
  exact (((start.comp fold).comp (snd ec (encodeList eb))).comp (listReverse eb b0)).congr _ (fun x => by
    simp only [Function.comp_apply,ListAlgorithms.pushMapWith,List.append_nil,List.reverse_reverse])

noncomputable def listFilterWith {p : γ × α → Bool}
    (P : PolyProgram (encodePair ec ea) encodeBool p) (a0 : α) (c0 : γ) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList ea) (fun x => x.2.filter (fun a => p (x.1,a))) := by
  let attach := (identity (encodePair ec ea)).listMapWith a0 (c0,a0)
  let filt := listFilter P (c0,a0)
  let drop := (snd ec ea).listMap (c0,a0)
  exact ((attach.comp filt).comp drop).congr _ (fun x => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.filterMapPair])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListExtras -/
section
namespace OAI


                                        
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace WordTransducer

def listBits : Transducer where
  Q := Unit
  initial := ()
  next _ b := ((),[true,b,false])
  finish _ := []
theorem listBits_run (xs : List Bool) : listBits.run () xs=encodeList encodeBool xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      change [true,b,false]++listBits.run () xs=quote [b]++encodeList encodeBool xs
      rw [ih]
      rfl
end WordTransducer
namespace PolyProgram
variable {α β γ : Type} {ea : α → List Bool} {eb : β → List Bool} {ec : γ → List Bool}
noncomputable def wordAsList : PolyProgram id (encodeList encodeBool) id :=
  WordTransducer.listBits.program.of_word (fun xs => WordTransducer.listBits_run xs)
noncomputable def natAsList : PolyProgram Nat.bits (encodeList encodeBool) Nat.bits :=
  wordAsList.recode Nat.bits (fun _ => rfl) (fun _ => rfl)
noncomputable def natSize : PolyProgram Nat.bits Nat.bits Nat.size :=
  (natAsList.comp (listLength encodeBool false)).congr _ (fun n => Nat.size_eq_bits_len n)
noncomputable def listFlatten (ea : α → List Bool) (a0 : α) :
    PolyProgram (encodeList (encodeList ea)) (encodeList ea) List.flatten := by
  let P := (listAppend ea a0).listFoldLinear [] 1 (by
    intro bs as
    simp only [EncodedList.append,List.length_append]
    omega)
  exact (((identity (encodeList (encodeList ea))).fanout (constant (encodeList (encodeList ea)) (encodeList ea) [])).comp P).congr _ (fun xs => by
    change xs.foldl (fun b a => b++a) []=xs.flatten
    have he (xs : List (List α)) (acc : List α) : xs.foldl (fun b a => b++a) acc=acc++xs.flatten := by
      induction xs generalizing acc with
      | nil => simp
      | cons y ys hi => simpa only [List.foldl_cons,List.flatten_cons,List.append_assoc] using hi (acc++y)
    simpa using he xs [])
noncomputable def listFlatMap {f : α → List β} (P : PolyProgram ea (encodeList eb) f) (a0 : α) (b0 : β) :
    PolyProgram (encodeList ea) (encodeList eb) (fun xs => xs.flatMap f) :=
  ((P.listMap a0).comp (listFlatten eb b0)).congr _ (fun xs => by rfl)
noncomputable def listFlatMapWith {f : γ × α → List β} (P : PolyProgram (encodePair ec ea) (encodeList eb) f) (a0 : α) (b0 : β) :
    PolyProgram (encodePair ec (encodeList ea)) (encodeList eb) (fun x => x.2.flatMap (fun a => f (x.1,a))) :=
  ((P.listMapWith a0 []).comp (listFlatten eb b0)).congr _ (fun x => by rfl)
noncomputable def listAllWith {p : γ × α → Bool} (P : PolyProgram (encodePair ec ea) encodeBool p) (a0 : α) :
    PolyProgram (encodePair ec (encodeList ea)) encodeBool (fun x => x.2.all (fun a => p (x.1,a))) :=
  ((P.listMapWith a0 false).comp (listAll (identity encodeBool) false)).congr _ (fun x => by simp only [Function.comp_apply,List.all_map,Function.id_comp])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinarySubtraction -/
section
namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Word
 def borrowBit (a b c : Bool) : Bool := ((!a) && b) || ((!a) && c) || (b && c)
 theorem fullSubtract (a b c : Bool) :
    a.toNat+2*(borrowBit a b c).toNat=b.toNat+c.toNat+(sumBit a b c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

 def sub : List Bool → List Bool → Bool → Bool × List Bool
  | [],[],c => (c,[])
  | a::xs,ys,c =>
      let t := sub xs ys.tail (borrowBit a (ys.head?.getD false) c)
      (t.1,sumBit a (ys.head?.getD false) c::t.2)
  | [],b::ys,c =>
      let t := sub [] ys (borrowBit false b c)
      (t.1,sumBit false b c::t.2)
termination_by xs ys _ => xs.length+ys.length

 theorem sub_step (xs ys : List Bool) (c : Bool) (h : (xs.isEmpty && ys.isEmpty)=false) :
    sub xs ys c=
      let t := sub xs.tail ys.tail (borrowBit (xs.head?.getD false) (ys.head?.getD false) c)
      (t.1,sumBit (xs.head?.getD false) (ys.head?.getD false) c::t.2) := by
  cases xs <;> cases ys <;> simp_all [sub]

 theorem value_lt (xs : List Bool) : value xs<2^xs.length := by
  induction xs with
  | nil => decide
  | cons b xs ih =>
      have hb : b.toNat≤1 := by cases b <;> decide
      simp only [value_cons,List.length_cons,pow_succ]
      omega

 theorem value_sub (xs ys : List Bool) (c : Bool) :
    value (sub xs ys c).2+value ys+c.toNat=
      value xs+2^(sub xs ys c).2.length*(sub xs ys c).1.toNat := by
  induction xs generalizing ys c with
  | nil =>
      induction ys generalizing c with
      | nil => simp [sub,value]
      | cons b ys ih =>
          rw [sub]
          simp only [value_cons,value_nil,List.length_cons,pow_succ]
          have h := ih (borrowBit false b c)
          have hb := fullSubtract false b c
          simp only [value_nil,Bool.toNat_false] at h hb
          nlinarith
  | cons a xs ih =>
      rw [sub]
      simp only [value_cons,List.length_cons,pow_succ]
      have h := ih ys.tail (borrowBit a (ys.head?.getD false) c)
      have hb := fullSubtract a (ys.head?.getD false) c
      cases ys with
      | nil =>
          simp only [value_nil,List.head?_nil,Option.getD_none,List.tail_nil,Bool.toNat_false] at *
          nlinarith
      | cons b ys =>
          simp only [value_cons,List.head?_cons,Option.getD_some,List.tail_cons] at *
          nlinarith

 theorem sub_borrow (xs ys : List Bool) : (sub xs ys false).1=decide (value xs<value ys) := by
  have h := value_sub xs ys false
  have hl := value_lt (sub xs ys false).2
  cases he : (sub xs ys false).1
  · simp only [he,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at h
    have hn : ¬ value xs<value ys := by omega
    simp only [decide_eq_false hn]
  · simp only [he,Bool.toNat_true,Bool.toNat_false,Nat.mul_one,Nat.add_zero] at h
    have hn : value xs<value ys := by omega
    simp only [decide_eq_true hn]

 theorem sub_clamp (xs ys : List Bool) :
    value (if (sub xs ys false).1 then [] else (sub xs ys false).2)=value xs-value ys := by
  have h := value_sub xs ys false
  cases he : (sub xs ys false).1
  · simp only [he,Bool.toNat_false,Nat.mul_zero,Nat.add_zero] at h
    simp only [Bool.false_eq_true,ite_false]
    omega
  · have hl := sub_borrow xs ys
    rw [he] at hl
    have hn : value xs<value ys := of_decide_eq_true hl.symm
    simp only [ite_true,value_nil]
    omega
end Word

namespace SubtractionLoop
open AdditionLoop (S ec ey enc enc_length)
 def next (s : S) : S :=
  (s.1.tail,(s.2.1.tail,(Word.borrowBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1,
    Word.sumBit (s.1.head?.getD false) (s.2.1.head?.getD false) s.2.2.1 :: s.2.2.2)))
 def finish (s : S) : Bool × List Bool := (s.2.2.1,s.2.2.2.reverse)
 def body (s : S) : (Bool × List Bool) ⊕ S := if AdditionLoop.empty s then .inl (finish s) else .inr (next s)
 def result (s : S) : Bool × List Bool :=
  let t := Word.sub s.1 s.2.1 s.2.2.1
  (t.1,s.2.2.2.reverse++t.2)

noncomputable def program : PolyProgram enc (encodeLoop enc ec) body := by
  let px := PolyProgram.fst id ey
  let pyz := PolyProgram.snd id ey
  let py := pyz.comp (PolyProgram.fst id ec)
  let pca := pyz.comp (PolyProgram.snd id ec)
  let pc := pca.comp (PolyProgram.fst encodeBool id)
  let pa := pca.comp (PolyProgram.snd encodeBool id)
  let bits := (px.comp PolyProgram.head).fanout ((py.comp PolyProgram.head).fanout pc)
  let binj := encodePair_injective encodeBool_injective (encodePair_injective encodeBool_injective encodeBool_injective)
  let sb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.sumBit v.1 v.2.1 v.2.2) binj)
  let cb := bits.comp (PolyProgram.boolFunction _ encodeBool (fun v : Bool × (Bool × Bool) => Word.borrowBit v.1 v.2.1 v.2.2) binj)
  let na := (sb.fanout pa).comp PolyProgram.cons
  let pn := (px.comp PolyProgram.tail).fanout ((py.comp PolyProgram.tail).fanout (cb.fanout na))
  let pe := ((px.comp PolyProgram.isEmpty).fanout (py.comp PolyProgram.isEmpty)).comp PolyProgram.boolAnd
  let pf := pc.fanout (pa.comp PolyProgram.reverse)
  exact (PolyProgram.ite pe (pn.comp (PolyProgram.injectRight enc ec))
    (pf.comp (PolyProgram.injectLeft enc ec))).congr _ (fun _ => rfl)

 theorem next_result (s : S) (h : AdditionLoop.empty s=false) : result (next s)=result s := by
  simp only [result]
  rw [Word.sub_step s.1 s.2.1 s.2.2.1 h]
  simp only [next,List.reverse_cons,List.append_assoc,List.singleton_append]

 theorem next_size (s : S) (h : AdditionLoop.empty s=false) : (enc (next s)).length≤(enc s).length := by
  have hs := AdditionLoop.shorten s h
  simp only [enc_length,next,List.length_cons]
  omega

 theorem run (L : ℕ) : ∀ (s : S) (S : ℕ), s.1.length+s.2.1.length=L → (enc s).length≤S →
    ∃ n≤L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL hs
      cases he : AdditionLoop.empty s with
      | true =>
          refine ⟨1,by omega,BoundedRun.stop hs ?_⟩
          rcases s with ⟨xs,ys,c,acc⟩
          have hz : xs=[] ∧ ys=[] := by simpa only [AdditionLoop.empty,Bool.and_eq_true,List.isEmpty_iff] using he
          rcases hz with ⟨rfl,rfl⟩
          simp [body,AdditionLoop.empty,finish,result,Word.sub]
      | false =>
          have hl : (next s).1.length+(next s).2.1.length<L := by simpa only [next,hL] using AdditionLoop.shorten s he
          obtain ⟨n,hn,hr⟩ := ih _ hl (next s) S rfl ((next_size s he).trans hs)
          refine ⟨n+1,by omega,?_⟩
          rw [next_result s he] at hr
          exact BoundedRun.step hs (by simp only [body,he,Bool.false_eq_true,ite_false]) hr

noncomputable def loop : PolyProgram enc ec result :=
  program.loop result (X+1) X (fun s => by
    obtain ⟨n,hn,hr⟩ := run (s.1.length+s.2.1.length) s (enc s).length rfl le_rfl
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc_length]; omega
    · simpa only [eval_X] using hr)
end SubtractionLoop

namespace PolyProgram
noncomputable def subWords : PolyProgram (encodePair id id) AdditionLoop.ec (fun x : List Bool × List Bool => Word.sub x.1 x.2 false) := by
  let ex : List Bool × List Bool → List Bool := encodePair id id
  let init := (fst id id).fanout ((snd id id).fanout (constant ex AdditionLoop.ec (false,[])))
  exact (init.comp SubtractionLoop.loop).congr _ (fun _ => rfl)

noncomputable def natLT : PolyProgram (encodePair Nat.bits Nat.bits) encodeBool (fun x : ℕ × ℕ => decide (x.1<x.2)) :=
  (subWords.comp (fst encodeBool id)).recode (fun x => (x.1.bits,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.sub_borrow,Word.value_bits])

noncomputable def natSub : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1-x.2) := by
  let clamp := ite (fst encodeBool id) (snd encodeBool id) (constant AdditionLoop.ec id [])
  exact ((subWords.comp clamp).comp toBits).recode (fun x => (x.1.bits,x.2.bits)) (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,Word.sub_clamp,Word.value_bits])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryDivision -/
section
namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace DivisionLoop
 def qstep (b : Bool) (d q r : ℕ) : ℕ := Nat.bit (!decide (Nat.bit b r<d)) q
 def rstep (b : Bool) (d r : ℕ) : ℕ := if Nat.bit b r<d then Nat.bit b r else Nat.bit b r-d

 theorem step_total (b : Bool) (d q r : ℕ) :
    qstep b d q r*d+rstep b d r=2*(q*d+r)+b.toNat := by
  by_cases ht : Nat.bit b r<d
  · rw [qstep,rstep,if_pos ht,decide_eq_true ht]
    simp only [Bool.not_true,Nat.bit_val,Bool.toNat_false]
    ring
  · have hd : d≤Nat.bit b r := by omega
    have he := Nat.sub_add_cancel hd
    rw [qstep,rstep,if_neg ht,decide_eq_false ht]
    simp only [Bool.not_false,Nat.bit_val,Bool.toNat_true] at *
    nlinarith

 theorem step_remainder (b : Bool) (d r : ℕ) (_ : 0<d) (hr : r<d) : rstep b d r<d := by
  have hb : b.toNat≤1 := by cases b <;> decide
  unfold rstep
  split_ifs with ht
  · exact ht
  · simp only [Nat.bit_val] at *
    omega

 def eval : List Bool → ℕ → ℕ → ℕ → ℕ × ℕ
  | [],_,q,r => (q,r)
  | b::xs,d,q,r => eval xs d (qstep b d q r) (rstep b d r)

 theorem eval_spec (xs : List Bool) (d q r : ℕ) (hd : 0<d) (hr : r<d) :
    (eval xs d q r).2<d ∧
      (eval xs d q r).1*d+(eval xs d q r).2=2^xs.length*(q*d+r)+Word.value xs.reverse := by
  induction xs generalizing q r with
  | nil => exact ⟨hr,by simp [eval]⟩
  | cons b xs ih =>
      obtain ⟨hrem,heq⟩ := ih (qstep b d q r) (rstep b d r) (step_remainder b d r hd hr)
      refine ⟨hrem,?_⟩
      change (eval xs d (qstep b d q r) (rstep b d r)).1*d+
        (eval xs d (qstep b d q r) (rstep b d r)).2=_
      rw [heq,step_total]
      simp only [List.length_cons,List.reverse_cons,Word.value_append,Word.value_cons,Word.value_nil,
        Nat.mul_zero,Nat.add_zero,List.length_reverse,pow_succ]
      ring

abbrev S := List Bool × (ℕ × (ℕ × ℕ))
abbrev eqr : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
abbrev edqr : ℕ × (ℕ × ℕ) → List Bool := encodePair Nat.bits eqr
abbrev enc : S → List Bool := encodePair id edqr
 def next (s : S) : S :=
  (s.1.tail,(s.2.1,(qstep (s.1.head?.getD false) s.2.1 s.2.2.1 s.2.2.2,
    rstep (s.1.head?.getD false) s.2.1 s.2.2.2)))
 def body (s : S) : (ℕ × ℕ) ⊕ S := if s.1.isEmpty then .inl s.2.2 else .inr (next s)
 def result (s : S) : ℕ × ℕ := eval s.1 s.2.1 s.2.2.1 s.2.2.2
 def potential (s : S) : ℕ := s.1.length+max s.2.2.1.bits.length s.2.2.2.bits.length

 theorem enc_length (s : S) :
    (enc s).length=2*s.1.length+2*s.2.1.bits.length+2*s.2.2.1.bits.length+s.2.2.2.bits.length+3 := by
  simp only [enc,edqr,eqr,encodePair_length,id_eq]
  omega

 theorem total_le_length (s : S) : potential s+s.2.1.bits.length≤(enc s).length := by
  simp only [potential,enc_length]
  omega

 theorem length_le_total (s : S) : (enc s).length≤3*(potential s+s.2.1.bits.length)+3 := by
  simp only [potential,enc_length]
  omega

 theorem next_potential (s : S) (h : s.1.isEmpty=false) : potential (next s)≤potential s := by
  have hx : s.1.tail.length<s.1.length := by
    cases hh : s.1 with
    | nil => simp only [hh,List.isEmpty_nil] at h; contradiction
    | cons b xs => simp only [List.tail_cons,List.length_cons]; omega
  have hq := NatBinary.bit_length (!decide (Nat.bit (s.1.head?.getD false) s.2.2.2<s.2.1)) s.2.2.1
  have hr := NatBinary.bit_length (s.1.head?.getD false) s.2.2.2
  have hrle : rstep (s.1.head?.getD false) s.2.1 s.2.2.2≤Nat.bit (s.1.head?.getD false) s.2.2.2 := by
    unfold rstep
    split_ifs <;> omega
  have hrl := (NatBinary.length_mono hrle).trans hr
  simp only [potential,next,qstep]
  omega

 theorem next_result (s : S) (h : s.1.isEmpty=false) : result (next s)=result s := by
  rcases s with ⟨xs,d,q,r⟩
  cases xs with
  | nil => contradiction
  | cons b xs => rfl

noncomputable def program : PolyProgram enc (encodeLoop enc eqr) body := by
  let px := PolyProgram.fst id edqr
  let pdqr := PolyProgram.snd id edqr
  let pd := pdqr.comp (PolyProgram.fst Nat.bits eqr)
  let pqr := pdqr.comp (PolyProgram.snd Nat.bits eqr)
  let pq := pqr.comp (PolyProgram.fst Nat.bits Nat.bits)
  let pr := pqr.comp (PolyProgram.snd Nat.bits Nat.bits)
  let pb := px.comp PolyProgram.head
  let pt := (pb.fanout pr).comp PolyProgram.natBit
  let plt := (pt.fanout pd).comp PolyProgram.natLT
  let nq := ((plt.comp PolyProgram.boolNot).fanout pq).comp PolyProgram.natBit
  let nr := PolyProgram.ite plt ((pt.fanout pd).comp PolyProgram.natSub) pt
  let pn := (px.comp PolyProgram.tail).fanout (pd.fanout (nq.fanout nr))
  exact (PolyProgram.ite (px.comp PolyProgram.isEmpty)
    (pn.comp (PolyProgram.injectRight enc eqr))
    (pqr.comp (PolyProgram.injectLeft enc eqr))).congr _ (fun s => by
      simp only [Function.comp_apply,body,next,qstep,rstep,decide_eq_true_eq])

 theorem run (xs : List Bool) (d q r S : ℕ) (hs : 3*(potential (xs,d,q,r)+d.bits.length)+3≤S) :
    BoundedRun enc body S (xs.length+1) (xs,d,q,r) (result (xs,d,q,r)) := by
  induction xs generalizing q r with
  | nil =>
      exact BoundedRun.stop ((length_le_total ([],d,q,r)).trans hs) rfl
  | cons b xs ih =>
      let s : DivisionLoop.S := (b::xs,d,q,r)
      have hp := next_potential s rfl
      change 3*(potential s+d.bits.length)+3≤S at hs
      have hnext : 3*(potential (next s)+d.bits.length)+3≤S := by omega
      have hr := ih (qstep b d q r) (rstep b d r) hnext
      have hh : result (xs,d,qstep b d q r,rstep b d r)=result s := rfl
      rw [hh] at hr
      exact BoundedRun.step ((length_le_total s).trans hs) rfl hr

noncomputable def loop : PolyProgram enc eqr result :=
  program.loop result (X+1) (3*X+3) (fun s => by
    refine ⟨s.1.length+1,?_,?_⟩
    · simp only [Polynomial.eval_add,eval_X,eval_one,enc_length]; omega
    · have hs := total_le_length s
      simpa only [Polynomial.eval_add,eval_mul,eval_ofNat,eval_X] using
        run s.1 s.2.1 s.2.2.1 s.2.2.2 (3*(enc s).length+3) (by
          change 3*(potential s+s.2.1.bits.length)+3≤3*(enc s).length+3
          omega))
end DivisionLoop

namespace PolyProgram
noncomputable def natDivMod : PolyProgram (encodePair Nat.bits Nat.bits) (encodePair Nat.bits Nat.bits)
    (fun x : ℕ × ℕ => (x.1/x.2,x.1%x.2)) := by
  let ex : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
  let px := fst Nat.bits Nat.bits
  let pd := snd Nat.bits Nat.bits
  let rev : PolyProgram Nat.bits id (fun n => n.bits.reverse) := reverse.recode Nat.bits (fun _ => rfl) (fun _ => rfl)
  let init := (px.comp rev).fanout (pd.fanout (constant ex DivisionLoop.eqr (0,0)))
  let normal := init.comp DivisionLoop.loop
  let zeroCase := (constant ex Nat.bits 0).fanout px
  refine (ite (pd.comp natZero) normal zeroCase).congr _ ?_
  intro x
  change (if decide (x.2=0) then (0,x.1) else DivisionLoop.eval x.1.bits.reverse x.2 0 0)=_
  by_cases hd : x.2=0
  · simp only [hd,decide_true,ite_true,Nat.div_zero,Nat.mod_zero]
  · simp only [decide_eq_false hd,Bool.false_eq_true,ite_false]
    obtain ⟨hr,he⟩ := DivisionLoop.eval_spec x.1.bits.reverse x.2 0 0 (Nat.pos_of_ne_zero hd) (Nat.pos_of_ne_zero hd)
    simp only [zero_mul,zero_add,mul_zero,zero_add,List.reverse_reverse,Word.value_bits] at he
    have hp : x.1/x.2=(DivisionLoop.eval x.1.bits.reverse x.2 0 0).1 ∧
        x.1%x.2=(DivisionLoop.eval x.1.bits.reverse x.2 0 0).2 :=
      (Nat.div_mod_unique (Nat.pos_of_ne_zero hd)).mpr ⟨by
        simpa only [Nat.mul_comm,Nat.add_comm] using he,hr⟩
    exact Prod.ext hp.1.symm hp.2.symm

noncomputable def natDiv : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1/x.2) :=
  (natDivMod.comp (fst Nat.bits Nat.bits)).congr _ (fun _ => rfl)
noncomputable def natMod : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1%x.2) :=
  (natDivMod.comp (snd Nat.bits Nat.bits)).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryGCD -/
section
namespace OAI


                                 
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace NatBinary
 theorem mod_length_lt {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) : (a%b).bits.length < a.bits.length := by
  have ha : 0 < a := hb.trans_le hba
  by_cases hz : a%b=0
  · rw [hz,Nat.zero_bits,List.length_nil]
    apply List.length_pos_iff.mpr
    intro h
    have := (zero_iff a).mp h
    omega
  · have hr := Nat.mod_lt a hb
    have he := Nat.mod_add_div a b
    have hq : 1 ≤ a/b := (Nat.le_div_iff_mul_le hb).mpr (by simpa only [one_mul] using hba)
    have hm : b ≤ b*(a/b) := by nlinarith
    have hsmall : 2*(a%b) < a := by omega
    have hlen := length_mono hsmall.le
    have hbit : (2*(a%b)).bits.length=(a%b).bits.length+1 := by
      have hn : Nat.bit false (a%b) ≠ 0 := by
        simp only [Nat.bit_val,Bool.toNat_false,Nat.add_zero]
        omega
      simpa only [Nat.size_eq_bits_len,Nat.bit_val,Bool.toNat_false,Nat.add_zero,Nat.succ_eq_add_one]
        using Nat.size_bit hn
    omega
end NatBinary

namespace GCDLoop
abbrev S := ℕ × ℕ
abbrev enc : S → List Bool := encodePair Nat.bits Nat.bits
 def next (s : S) : S := (s.2,s.1%s.2)
 def body (s : S) : ℕ ⊕ S := if s.2=0 then .inl s.1 else .inr (next s)
 def result (s : S) : ℕ := s.1.gcd s.2
 def potential (s : S) : ℕ := s.1.bits.length+s.2.bits.length

 theorem enc_length (s : S) : (enc s).length=2*s.1.bits.length+1+s.2.bits.length := by
  exact encodePair_length _ _ _
 theorem length_le_potential (s : S) : (enc s).length ≤ 2*potential s+1 := by
  simp only [enc_length,potential]; omega
 theorem potential_le_length (s : S) : potential s ≤ (enc s).length := by
  simp only [enc_length,potential]; omega

 theorem next_result (s : S) : result (next s)=result s := by
  simp only [result,next]
  calc s.2.gcd (s.1%s.2)=(s.1%s.2).gcd s.2 := Nat.gcd_comm _ _
    _=s.2.gcd s.1 := (Nat.gcd_rec _ _).symm
    _=s.1.gcd s.2 := Nat.gcd_comm _ _

 theorem next_potential (s : S) : potential (next s) ≤ potential s := by
  have hm := NatBinary.length_mono (Nat.mod_le s.1 s.2)
  simp only [potential,next]
  omega

 theorem next_potential_lt (s : S) (ho : s.2 ≤ s.1) (hb : s.2 ≠ 0) : potential (next s) < potential s := by
  have h := NatBinary.mod_length_lt (Nat.pos_of_ne_zero hb) ho
  simp only [potential,next]
  omega

noncomputable def program : PolyProgram enc (encodeLoop enc Nat.bits) body := by
  let px := PolyProgram.fst Nat.bits Nat.bits
  let py := PolyProgram.snd Nat.bits Nat.bits
  let pn := py.fanout PolyProgram.natMod
  exact (PolyProgram.ite (py.comp PolyProgram.natZero)
    (pn.comp (PolyProgram.injectRight enc Nat.bits))
    (px.comp (PolyProgram.injectLeft enc Nat.bits))).congr _ (fun _ => by
      simp only [Function.comp_apply,body,next,decide_eq_true_eq])

 theorem run_ordered (L : ℕ) : ∀ (s : S) (S : ℕ), potential s=L →
    s.2 ≤ s.1 → 2*L+1 ≤ S → ∃ n ≤ L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL ho hs
      have hsize : (enc s).length ≤ S := (length_le_potential s).trans (by omega)
      by_cases hz : s.2=0
      · refine ⟨1,by omega,BoundedRun.stop hsize ?_⟩
        simp only [body,hz,ite_true,result,Nat.gcd_zero_right]
      · have hpot : potential (next s) < L := by simpa only [hL] using next_potential_lt s ho hz
        have horder : (next s).2 ≤ (next s).1 := (Nat.mod_lt s.1 (Nat.pos_of_ne_zero hz)).le
        obtain ⟨n,hn,hr⟩ := ih _ hpot (next s) S rfl horder (by omega)
        refine ⟨n+1,by omega,?_⟩
        rw [next_result] at hr
        exact BoundedRun.step hsize (by simp only [body,hz,ite_false]) hr

 theorem run (s : S) (S : ℕ) (hs : 2*potential s+1 ≤ S) :
    ∃ n ≤ potential s+2, BoundedRun enc body S n s (result s) := by
  by_cases ho : s.2 ≤ s.1
  · obtain ⟨n,hn,hr⟩ := run_ordered (potential s) s S rfl ho hs
    exact ⟨n,by omega,hr⟩
  · have hb : s.2 ≠ 0 := by omega
    have hn := next_potential s
    have horder : (next s).2 ≤ (next s).1 := (Nat.mod_lt s.1 (Nat.pos_of_ne_zero hb)).le
    obtain ⟨n,hbound,hr⟩ := run_ordered (potential (next s)) (next s) S rfl horder (by omega)
    refine ⟨n+1,by omega,?_⟩
    rw [next_result] at hr
    exact BoundedRun.step ((length_le_potential s).trans hs)
      (by simp only [body,hb,ite_false]) hr

noncomputable def loop : PolyProgram enc Nat.bits result :=
  program.loop result (X+2) (2*X+1) (fun s => by
    have hs := potential_le_length s
    obtain ⟨n,hn,hr⟩ := run s (2*(enc s).length+1) (by omega)
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_ofNat]; omega
    · simpa only [eval_add,eval_mul,eval_ofNat,eval_one,eval_X] using hr)
end GCDLoop

namespace PolyProgram
noncomputable def natGcd : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1.gcd x.2) :=
  GCDLoop.loop
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryMultiplication -/
section
namespace OAI


                                            
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace MultiplicationLoop
abbrev S := ℕ × (ℕ × ℕ)
abbrev ey : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
abbrev enc : S → List Bool := encodePair Nat.bits ey
 def next (s : S) : S := (s.1.div2,(Nat.bit false s.2.1,if s.1.bodd then s.2.2+s.2.1 else s.2.2))
 def body (s : S) : ℕ ⊕ S := if s.1=0 then .inl s.2.2 else .inr (next s)
 def result (s : S) : ℕ := s.1*s.2.1+s.2.2
 def potential (s : S) : ℕ := s.1.bits.length+max s.2.1.bits.length s.2.2.bits.length

 theorem enc_length (s : S) : (enc s).length=2*s.1.bits.length+2*s.2.1.bits.length+s.2.2.bits.length+2 := by
  simp only [enc,ey,encodePair_length]
  omega

 theorem potential_le_length (s : S) : potential s≤(enc s).length := by
  simp only [potential,enc_length]
  omega

 theorem length_le_potential (s : S) : (enc s).length≤3*potential s+2 := by
  simp only [potential,enc_length]
  omega

 theorem next_potential (s : S) (h : s.1≠0) : potential (next s)≤potential s := by
  have hx := NatBinary.half_lt_length h
  have hy := NatBinary.bit_length false s.2.1
  have ha := NatBinary.add_length s.2.2 s.2.1
  simp only [potential,next]
  cases s.1.bodd <;> simp only [Bool.false_eq_true,ite_false,ite_true] <;> omega

 theorem next_result (s : S) : result (next s)=result s := by
  have h := Nat.bodd_add_div2 s.1
  simp only [result,next,Nat.bit_val,Bool.toNat_false,Nat.add_zero]
  cases he : s.1.bodd
  · simp only [he,Bool.toNat_false,zero_add] at h
    simp only [Bool.false_eq_true,ite_false]
    nlinarith only [congrArg (fun n => n*s.2.1) h]
  · simp only [he,Bool.toNat_true] at h
    simp only [ite_true]
    nlinarith only [congrArg (fun n => n*s.2.1) h]

noncomputable def program : PolyProgram enc (encodeLoop enc Nat.bits) body := by
  let px := PolyProgram.fst Nat.bits ey
  let pyz := PolyProgram.snd Nat.bits ey
  let py := pyz.comp (PolyProgram.fst Nat.bits Nat.bits)
  let pa := pyz.comp (PolyProgram.snd Nat.bits Nat.bits)
  let half := px.comp PolyProgram.natHalf
  let twice := ((PolyProgram.constant enc encodeBool false).fanout py).comp PolyProgram.natBit
  let acc := PolyProgram.ite (px.comp PolyProgram.natOdd) pa ((pa.fanout py).comp PolyProgram.natAdd)
  let pn := half.fanout (twice.fanout acc)
  exact (PolyProgram.ite (px.comp PolyProgram.natZero)
    (pn.comp (PolyProgram.injectRight enc Nat.bits))
    (pa.comp (PolyProgram.injectLeft enc Nat.bits))).congr _ (fun s => by
      simp only [Function.comp_apply,body,decide_eq_true_eq]
      rfl)

 theorem run (L : ℕ) : ∀ (s : S) (S : ℕ), s.1.bits.length=L → 3*potential s+2≤S →
    ∃ n≤L+1, BoundedRun enc body S n s (result s) := by
  induction L using Nat.strong_induction_on with
  | h L ih =>
      intro s S hL hs
      have hsize := (length_le_potential s).trans hs
      by_cases hz : s.1=0
      · refine ⟨1,by omega,BoundedRun.stop hsize ?_⟩
        simp only [body,hz,ite_true,result,zero_mul,zero_add]
      · have hl : (next s).1.bits.length<L := by simpa only [next,hL] using NatBinary.half_lt_length hz
        have hb : 3*potential (next s)+2≤S := by have := next_potential s hz; omega
        obtain ⟨n,hn,hr⟩ := ih _ hl (next s) S rfl hb
        refine ⟨n+1,by omega,?_⟩
        rw [next_result] at hr
        exact BoundedRun.step hsize (by simp only [body,hz,ite_false]) hr

noncomputable def loop : PolyProgram enc Nat.bits result :=
  program.loop result (X+1) (3*X+2) (fun s => by
    obtain ⟨n,hn,hr⟩ := run s.1.bits.length s (3*(enc s).length+2) rfl (by
      have := potential_le_length s; omega)
    refine ⟨n,?_,?_⟩
    · simp only [eval_add,eval_X,eval_one,enc_length]; omega
    · simpa only [eval_add,eval_mul,eval_ofNat,eval_X] using hr)
end MultiplicationLoop

namespace PolyProgram
noncomputable def natMul : PolyProgram (encodePair Nat.bits Nat.bits) Nat.bits (fun x : ℕ × ℕ => x.1*x.2) := by
  let ex : ℕ × ℕ → List Bool := encodePair Nat.bits Nat.bits
  let init := (fst Nat.bits Nat.bits).fanout ((snd Nat.bits Nat.bits).fanout (constant ex Nat.bits 0))
  exact (init.comp MultiplicationLoop.loop).congr _ (fun x => by
    simp only [Function.comp_apply,MultiplicationLoop.result,Nat.add_zero])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryInteger -/
section
namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Signed
 def value (s : Bool) (n : ℕ) : ℤ := if s then -(n:ℤ) else n
 def sign (z : ℤ) : Bool := decide (z < 0)
 def parts (z : ℤ) : Bool × ℕ := (sign z,z.natAbs)
 def encode (z : ℤ) : List Bool := encodePair encodeBool Nat.bits (parts z)

 theorem abs_value (s : Bool) (n : ℕ) : (value s n).natAbs=n := by cases s <;> simp [value]
 theorem sign_value (s : Bool) (n : ℕ) : sign (value s n)=(s && !decide (n=0)) := by
  cases s <;> by_cases hn : n=0
  all_goals simp only [value,sign,Bool.false_eq_true,ite_false,ite_true]
  all_goals simp [hn, Nat.pos_of_ne_zero]

 theorem value_parts (z : ℤ) : value (sign z) z.natAbs=z := by
  unfold value sign
  split_ifs with h
  · exact (Int.eq_neg_natAbs_of_nonpos (le_of_lt (of_decide_eq_true h))).symm
  · exact Int.natAbs_of_nonneg (by simpa using h)

 theorem value_neg (s : Bool) (n : ℕ) : value (!s) n= -value s n := by
  cases s <;> simp [value]

 theorem value_mul (s t : Bool) (n m : ℕ) : value (xor s t) (n*m)=value s n*value t m := by
  cases s <;> cases t <;> simp [value]

 def add (s t : Bool) (n m : ℕ) : ℤ :=
  if s=t then value s (n+m) else if n < m then value t (m-n) else value s (n-m)

 theorem value_add (s t : Bool) (n m : ℕ) : add s t n m=value s n+value t m := by
  cases s <;> cases t <;> by_cases h : n < m <;> simp [add,value,h] <;> omega

 theorem value_div (s : Bool) (n d : ℕ) (h : d∣n) : value s (n/d)=value s n/(d:ℤ) := by
  have hd : (d:ℤ)∣(n:ℤ) := Int.natCast_dvd_natCast.mpr h
  cases s <;> simp only [value,Bool.false_eq_true,ite_false,ite_true,Int.neg_ediv_of_dvd hd,Int.ofNat_ediv_ofNat]
end Signed

namespace PolyProgram
abbrev signedParts : Bool × ℕ → List Bool := encodePair encodeBool Nat.bits

noncomputable def intFromParts : PolyProgram signedParts Signed.encode (fun x => Signed.value x.1 x.2) := by
  let ps := fst encodeBool Nat.bits
  let pn := snd encodeBool Nat.bits
  let s := (ps.fanout ((pn.comp natZero).comp boolNot)).comp boolAnd
  exact (s.fanout pn).recode id (fun _ => rfl) (fun x => by
    simp only [Function.comp_apply,id_eq,Signed.encode,Signed.parts,Signed.sign_value,Signed.abs_value])

noncomputable def intSign : PolyProgram Signed.encode encodeBool Signed.sign :=
  (fst encodeBool Nat.bits).recode Signed.parts (fun _ => rfl) (fun _ => rfl)
noncomputable def intAbs : PolyProgram Signed.encode Nat.bits Int.natAbs :=
  (snd encodeBool Nat.bits).recode Signed.parts (fun _ => rfl) (fun _ => rfl)

noncomputable def intNeg : PolyProgram Signed.encode Signed.encode Neg.neg :=
  (((intSign.comp boolNot).fanout intAbs).comp intFromParts).congr _ (fun z => by
    simp only [Function.comp_apply,Signed.value_neg,Signed.value_parts])

noncomputable def intOfNat : PolyProgram Nat.bits Signed.encode Nat.cast :=
  (((constant Nat.bits encodeBool false).fanout (identity Nat.bits)).comp intFromParts).congr _ (fun _ => rfl)

noncomputable def boolXor : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => xor x.1 x.2) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)
noncomputable def boolEq : PolyProgram (encodePair encodeBool encodeBool) encodeBool (fun x => decide (x.1=x.2)) :=
  boolFunction _ _ _ (encodePair_injective encodeBool_injective encodeBool_injective)

noncomputable def intMul : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1*x.2) := by
  let px := fst Signed.encode Signed.encode
  let py := snd Signed.encode Signed.encode
  let s := ((px.comp intSign).fanout (py.comp intSign)).comp boolXor
  let n := ((px.comp intAbs).fanout (py.comp intAbs)).comp natMul
  exact ((s.fanout n).comp intFromParts).congr _ (fun x => by
    simp only [Function.comp_apply,Signed.value_mul,Signed.value_parts])

noncomputable def intAdd : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1+x.2) := by
  let px := fst Signed.encode Signed.encode
  let py := snd Signed.encode Signed.encode
  let sx := px.comp intSign
  let sy := py.comp intSign
  let nx := px.comp intAbs
  let ny := py.comp intAbs
  let plus := ((sx.fanout ((nx.fanout ny).comp natAdd)).comp intFromParts)
  let minusX := (sx.fanout ((nx.fanout ny).comp natSub)).comp intFromParts
  let minusY := (sy.fanout ((ny.fanout nx).comp natSub)).comp intFromParts
  let minus := ite ((nx.fanout ny).comp natLT) minusX minusY
  refine (ite ((sx.fanout sy).comp boolEq) minus plus).congr _ ?_
  intro x
  simpa only [Function.comp_apply, decide_eq_true_eq, Signed.add, Signed.value_parts]
    using Signed.value_add (Signed.sign x.1) (Signed.sign x.2) x.1.natAbs x.2.natAbs

noncomputable def intSub : PolyProgram (encodePair Signed.encode Signed.encode) Signed.encode (fun x : ℤ × ℤ => x.1-x.2) :=
  ((intNeg.second Signed.encode).comp intAdd).congr _ (fun x => (sub_eq_add_neg x.1 x.2).symm)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryRational -/
section
namespace OAI


                                      
section
namespace MetricKMedian.Binary
open Function Polynomial

namespace Ratio
 def parts (q : ℚ) : ℤ × ℕ := (q.num,q.den)
 def encode (q : ℚ) : List Bool := encodePair Signed.encode Nat.bits (parts q)
 def normalized (x : ℤ × ℕ) : ℤ × ℕ :=
  if x.2=0 then (0,1) else
    (Signed.value (Signed.sign x.1) (x.1.natAbs / x.2.gcd x.1.natAbs),x.2 / x.2.gcd x.1.natAbs)
 theorem normalized_eq (x : ℤ × ℕ) : normalized x=parts (mkRat x.1 x.2) := by
  simp only [normalized,parts,Rat.num_mkRat,Rat.den_mkRat]
  split_ifs with h
  · rfl
  · rw [Signed.value_div _ _ _ (Nat.gcd_dvd_right _ _),Signed.value_parts]

 theorem inv_eq (q : ℚ) : q⁻¹=mkRat (Signed.value (Signed.sign q.num) q.den) q.num.natAbs := by
  rw [Rat.mkRat_eq_div]
  calc
    q⁻¹ = ((q.num:ℚ)/q.den)⁻¹ := congrArg Inv.inv q.num_div_den.symm
    _ = (q.den:ℚ)/q.num := inv_div _ _
    _ = _ := by
      have hnum := Signed.value_parts q.num
      unfold Signed.value at hnum ⊢
      split_ifs with hn
      · rw [if_pos hn] at hnum
        have haZ : (q.num.natAbs:ℤ) = -q.num := by omega
        have ha : (q.num.natAbs:ℚ) = -(q.num:ℚ) := by simpa only [Int.cast_natCast,Int.cast_neg] using congrArg (fun z : ℤ => (z:ℚ)) haZ
        rw [Int.cast_neg,Int.cast_natCast,ha,neg_div_neg_eq]
      · rw [if_neg hn] at hnum
        have ha : (q.num.natAbs:ℚ) = (q.num:ℚ) := by simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z:ℚ)) hnum
        rw [Int.cast_natCast,ha]
end Ratio

namespace PolyProgram
noncomputable def intLT : PolyProgram (encodePair Signed.encode Signed.encode) encodeBool (fun x : ℤ × ℤ => decide (x.1 < x.2)) :=
  (intSub.comp intSign).congr _ (fun _ => by simp only [Function.comp_apply,Signed.sign,sub_neg])
noncomputable def intEQ : PolyProgram (encodePair Signed.encode Signed.encode) encodeBool (fun x : ℤ × ℤ => decide (x.1=x.2)) :=
  ((intSub.comp intAbs).comp natZero).congr _ (fun _ => by simp only [Function.comp_apply,Int.natAbs_eq_zero,sub_eq_zero])

noncomputable def mkRational : PolyProgram (encodePair Signed.encode Nat.bits) Ratio.encode (fun x => mkRat x.1 x.2) := by
  let pn := fst Signed.encode Nat.bits
  let pd := snd Signed.encode Nat.bits
  let pa := pn.comp intAbs
  let pg := (pd.fanout pa).comp natGcd
  let nm := (((pn.comp intSign).fanout ((pa.fanout pg).comp natDiv)).comp intFromParts)
  let dm := (pd.fanout pg).comp natDiv
  let normal := ite (pd.comp natZero) (nm.fanout dm)
    (constant (encodePair Signed.encode Nat.bits) (encodePair Signed.encode Nat.bits) (0,1))
  refine normal.recode id (fun _ => rfl) ?_
  intro x
  simp only [Function.comp_apply,id_eq,decide_eq_true_eq]
  change encodePair Signed.encode Nat.bits (Ratio.normalized x)=Ratio.encode (mkRat x.1 x.2)
  rw [Ratio.normalized_eq]
  rfl

noncomputable def ratNum : PolyProgram Ratio.encode Signed.encode Rat.num :=
  (fst Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)
noncomputable def ratDen : PolyProgram Ratio.encode Nat.bits Rat.den :=
  (snd Signed.encode Nat.bits).recode Ratio.parts (fun _ => rfl) (fun _ => rfl)
noncomputable def ratNeg : PolyProgram Ratio.encode Ratio.encode Neg.neg := by
  refine (((ratNum.comp intNeg).fanout ratDen)).recode id (fun _ => rfl) ?_
  intro q
  simp only [Function.comp_apply,id_eq,Ratio.encode,Ratio.parts,Rat.num_neg_eq_neg_num,Rat.den_neg_eq_den]
noncomputable def ratOfInt : PolyProgram Signed.encode Ratio.encode Int.cast :=
  (((identity Signed.encode).fanout (constant Signed.encode Nat.bits 1)).comp mkRational).congr _ (fun z => by simp [Rat.mkRat_eq_div])
noncomputable def ratOfNat : PolyProgram Nat.bits Ratio.encode Nat.cast :=
  (intOfNat.comp ratOfInt).congr _ (fun n => by simp)
noncomputable def ratMul : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1*x.2) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let pn := ((px.comp ratNum).fanout (py.comp ratNum)).comp intMul
  let pd := ((px.comp ratDen).fanout (py.comp ratDen)).comp natMul
  exact ((pn.fanout pd).comp mkRational).congr _ (fun x => (Rat.mul_def' x.1 x.2).symm)
noncomputable def ratAdd : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1+x.2) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let pnx := ((px.comp ratNum).fanout ((py.comp ratDen).comp intOfNat)).comp intMul
  let pny := ((py.comp ratNum).fanout ((px.comp ratDen).comp intOfNat)).comp intMul
  let pn := (pnx.fanout pny).comp intAdd
  let pd := ((px.comp ratDen).fanout (py.comp ratDen)).comp natMul
  exact ((pn.fanout pd).comp mkRational).congr _ (fun x => (Rat.add_def' x.1 x.2).symm)
noncomputable def ratSub : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1-x.2) :=
  ((ratNeg.second Ratio.encode).comp ratAdd).congr _ (fun x => (sub_eq_add_neg x.1 x.2).symm)
noncomputable def ratInv : PolyProgram Ratio.encode Ratio.encode Inv.inv :=
  (((((ratNum.comp intSign).fanout ratDen).comp intFromParts).fanout (ratNum.comp intAbs)).comp mkRational).congr _ (fun q => (Ratio.inv_eq q).symm)
noncomputable def ratDiv : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => x.1/x.2) :=
  ((ratInv.second Ratio.encode).comp ratMul).congr _ (fun x => (div_eq_mul_inv x.1 x.2).symm)
noncomputable def ratLT : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1 < x.2)) := by
  let px := fst Ratio.encode Ratio.encode
  let py := snd Ratio.encode Ratio.encode
  let lhs := ((px.comp ratNum).fanout ((py.comp ratDen).comp intOfNat)).comp intMul
  let rhs := ((py.comp ratNum).fanout ((px.comp ratDen).comp intOfNat)).comp intMul
  refine ((lhs.fanout rhs).comp intLT).congr _ ?_
  intro x
  simp only [Function.comp_apply]
  simp only [← Rat.lt_iff]
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.GaussianKernel -/
section
namespace OAI

namespace MetricKMedian.Gaussian
open Finset

def residual {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1)) :
    Fin r → Fin n → ℚ :=
  fun i j => A i.succ (p.succAbove j) - A 0 (p.succAbove j)/A 0 p*A i.succ p

def lift {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1))
    (z : Fin n → ℚ) : Fin (n+1) → ℚ :=
  p.insertNth (-(∑ j, A 0 (p.succAbove j)/A 0 p*z j)) z

theorem lift_nonzero {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1))
    (z : Fin n → ℚ) (hz : ∃ j, z j ≠ 0) : ∃ j, lift A p z j ≠ 0 := by
  obtain ⟨j,hj⟩ := hz
  exact ⟨p.succAbove j, by simpa only [lift,Fin.insertNth_apply_succAbove] using hj⟩

theorem lift_kernel {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ) (p : Fin (n+1))
    (hp : A 0 p ≠ 0) (z : Fin n → ℚ)
    (hz : ∀ i, ∑ j, residual A p i j*z j=0) :
    ∀ i, ∑ j, A i j*lift A p z j=0 := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · rw [Fin.sum_univ_succAbove _ p]
    simp only [lift,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove,mul_neg]
    have hs : A 0 p*(∑ j, A 0 (p.succAbove j)/A 0 p*z j)=
        ∑ j, A 0 (p.succAbove j)*z j := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      field_simp
    rw [hs,neg_add_cancel]
  · rw [Fin.sum_univ_succAbove _ p]
    simp only [lift,Fin.insertNth_apply_same,Fin.insertNth_apply_succAbove]
    have hh := hz i
    simp only [residual,sub_mul,sum_sub_distrib] at hh
    have he : (∑ j, A 0 (p.succAbove j)/A 0 p*A i.succ p*z j)=
        A i.succ p*(∑ j, A 0 (p.succAbove j)/A 0 p*z j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      ring
    rw [he] at hh
    linarith

def kernel : (r n : ℕ) → (Fin r → Fin n → ℚ) → Fin n → ℚ
  | 0, _, _ => fun j => if j.val=0 then 1 else 0
  | _+1, 0, _ => Fin.elim0
  | r+1, n+1, A =>
    if h : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty then
      let p := (univ.filter (fun j => A 0 j ≠ 0)).min' h
      lift A p (kernel r n (residual A p))
    else kernel r (n+1) (fun i j => A i.succ j)

theorem kernel_spec (r n : ℕ) (A : Fin r → Fin n → ℚ) (hn : r < n) :
    (∃ j, kernel r n A j ≠ 0) ∧ (∀ i, ∑ j, A i j*kernel r n A j=0) := by
  induction r generalizing n with
  | zero =>
    have hn0 : 0 < n := hn
    refine ⟨⟨⟨0,hn0⟩,?_⟩,fun i => Fin.elim0 i⟩
    simp only [kernel,ite_true,ne_eq,one_ne_zero,not_false_eq_true]
  | succ r ih =>
    cases n with
    | zero => omega
    | succ n =>
      by_cases hh : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty
      · let p := (univ.filter (fun j => A 0 j ≠ 0)).min' hh
        have hp : A 0 p ≠ 0 := (mem_filter.mp (min'_mem _ hh)).2
        have hi := ih n (residual A p) (by omega)
        change (∃ j, (if h : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty then
            lift A ((univ.filter (fun j => A 0 j ≠ 0)).min' h)
              (kernel r n (residual A ((univ.filter (fun j => A 0 j ≠ 0)).min' h)))
            else kernel r (n+1) (fun i j => A i.succ j)) j ≠ 0) ∧ _
        simp only [kernel,dif_pos hh]
        exact ⟨lift_nonzero A p _ hi.1,lift_kernel A p hp _ hi.2⟩
      · have hzero : ∀ j, A 0 j=0 := by
          intro j
          by_contra hj
          exact hh ⟨j,mem_filter.mpr ⟨mem_univ _,hj⟩⟩
        have hi := ih (n+1) (fun i j => A i.succ j) (by omega)
        have he : kernel (r+1) (n+1) A=kernel r (n+1) (fun i j => A i.succ j) := by
          rw [kernel,dif_neg hh]
        rw [he]
        refine ⟨hi.1,?_⟩
        intro i
        refine Fin.cases ?_ (fun i => hi.2 i) i
        simp only [hzero,zero_mul,sum_const_zero]

end MetricKMedian.Gaussian

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.GaussianCircuit -/
section
namespace OAI

namespace MetricKMedian.Gaussian
open Finset

def IsCircuit {r n : ℕ} (A : Fin r → Fin n → ℚ) (z : Fin n → ℚ) : Prop :=
  ∀ v : Fin n → ℚ, (∀ j, z j=0 → v j=0) → (∀ i, ∑ j, A i j*v j=0) →
    ∃ t : ℚ, ∀ j, v j=t*z j

theorem lift_eq_of_kernel {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (hp : A 0 p ≠ 0) (v : Fin (n+1) → ℚ)
    (h0 : ∑ j, A 0 j*v j=0) :
    v=lift A p (fun j => v (p.succAbove j)) := by
  have he : v p= -(∑ j, A 0 (p.succAbove j)/A 0 p*v (p.succAbove j)) := by
    rw [Fin.sum_univ_succAbove _ p] at h0
    have hs : A 0 p*(∑ j, A 0 (p.succAbove j)/A 0 p*v (p.succAbove j))=
        ∑ j, A 0 (p.succAbove j)*v (p.succAbove j) := by
      rw [mul_sum]
      apply sum_congr rfl
      intro j _
      field_simp
    apply (mul_left_cancel₀ hp)
    rw [mul_neg,hs]
    linarith
  funext j
  by_cases hj : j=p
  · subst j
    simpa only [lift,Fin.insertNth_apply_same] using he
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [lift,Fin.insertNth_apply_succAbove]

theorem residual_kernel {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (hp : A 0 p ≠ 0) (v : Fin (n+1) → ℚ)
    (hv : ∀ i, ∑ j, A i j*v j=0) :
    ∀ i, ∑ j, residual A p i j*v (p.succAbove j)=0 := by
  have he := lift_eq_of_kernel A p hp v (hv 0)
  intro i
  have hi := hv i.succ
  rw [Fin.sum_univ_succAbove _ p] at hi
  have hep := congrFun he p
  simp only [lift,Fin.insertNth_apply_same] at hep
  rw [hep] at hi
  simp only [residual,sub_mul,sum_sub_distrib]
  have hs : (∑ j, A 0 (p.succAbove j)/A 0 p*A i.succ p*v (p.succAbove j))=
      A i.succ p*(∑ j, A 0 (p.succAbove j)/A 0 p*v (p.succAbove j)) := by
    rw [mul_sum]
    apply sum_congr rfl
    intro j _
    ring
  rw [hs]
  linarith

theorem lift_smul {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (z : Fin n → ℚ) (t : ℚ) :
    lift A p (fun j => t*z j)=fun j => t*lift A p z j := by
  funext j
  by_cases hj : j=p
  · subst j
    simp only [lift,Fin.insertNth_apply_same]
    rw [mul_neg, mul_sum]
    congr 1
    apply sum_congr rfl
    intro i _
    ring
  · obtain ⟨k,rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [lift,Fin.insertNth_apply_succAbove]

theorem lift_circuit {r n : ℕ} (A : Fin (r+1) → Fin (n+1) → ℚ)
    (p : Fin (n+1)) (hp : A 0 p ≠ 0) (z : Fin n → ℚ)
    (hz : IsCircuit (residual A p) z) : IsCircuit A (lift A p z) := by
  intro v hs hv
  have hsub : ∀ j, z j=0 → v (p.succAbove j)=0 := by
    intro j hj
    apply hs
    simpa only [lift,Fin.insertNth_apply_succAbove] using hj
  obtain ⟨t,ht⟩ := hz (fun j => v (p.succAbove j)) hsub (residual_kernel A p hp v hv)
  refine ⟨t,?_⟩
  have he := lift_eq_of_kernel A p hp v (hv 0)
  rw [show (fun j => v (p.succAbove j))=(fun j => t*z j) from funext ht,lift_smul] at he
  exact congrFun he

theorem kernel_circuit (r n : ℕ) (A : Fin r → Fin n → ℚ) (hn : r < n) :
    (∃ j, kernel r n A j=1) ∧ IsCircuit A (kernel r n A) := by
  induction r generalizing n with
  | zero =>
    let j0 : Fin n := ⟨0,hn⟩
    refine ⟨⟨j0,by simp only [kernel,j0,ite_true]⟩,?_⟩
    intro v hs _
    refine ⟨v j0,?_⟩
    intro j
    by_cases hj : j.val=0
    · have he : j=j0 := Fin.ext hj
      subst j
      simp only [kernel,j0,ite_true,mul_one]
    · have hh := hs j (by simp only [kernel,if_neg hj])
      simp only [kernel,if_neg hj,mul_zero,hh]
  | succ r ih =>
    cases n with
    | zero => omega
    | succ n =>
      by_cases hh : (univ.filter (fun j => A 0 j ≠ 0)).Nonempty
      · let p := (univ.filter (fun j => A 0 j ≠ 0)).min' hh
        have hp : A 0 p ≠ 0 := (mem_filter.mp (min'_mem _ hh)).2
        obtain ⟨⟨j,hj⟩,hc⟩ := ih n (residual A p) (by omega)
        have he : kernel (r+1) (n+1) A=lift A p (kernel r n (residual A p)) := by
          rw [kernel,dif_pos hh]
        rw [he]
        refine ⟨⟨p.succAbove j,?_⟩,lift_circuit A p hp _ hc⟩
        simpa only [lift,Fin.insertNth_apply_succAbove] using hj
      · have hi := ih (n+1) (fun i j => A i.succ j) (by omega)
        have he : kernel (r+1) (n+1) A=kernel r (n+1) (fun i j => A i.succ j) := by
          rw [kernel,dif_neg hh]
        rw [he]
        refine ⟨hi.1,?_⟩
        intro v hs hv
        exact hi.2 v hs (fun i => hv i.succ)

end MetricKMedian.Gaussian

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.GramDependence -/
section
namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix

variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq C]

theorem gram_det_ne_zero (A : Matrix R C ℤ)
    (hi : LinearIndependent ℚ (fun c => fun r => (A r c:ℚ))) :
    (A.transpose*A).det ≠ 0 := by
  intro hz
  obtain ⟨v,hv,hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hz
  have hzero : A*ᵥv=0 := by
    have hh := congrArg (dotProduct v) hker
    rw [← mulVec_mulVec,dotProduct_mulVec,dotProduct_zero,vecMul_transpose,
      dotProduct_self_eq_zero] at hh
    exact hh
  have hlin : Function.Injective ((fun r c => (A r c:ℚ)) *ᵥ ·) :=
    Matrix.mulVec_injective_iff.mpr hi
  have hcast : (fun r c => (A r c:ℚ))*ᵥ(fun c => (v c:ℚ))=0 := by
    ext r
    have hh := congrFun hzero r
    change (∑ c, A r c*v c)=0 at hh
    change (∑ c, (A r c:ℚ)*(v c:ℚ))=0
    exact_mod_cast hh
  have hvQ := hlin (hcast.trans (mulVec_zero _).symm)
  apply hv
  ext c
  have hh := congrFun hvQ c
  change (v c:ℚ)=0 at hh
  change v c=0
  exact_mod_cast hh

theorem gram_span_relation (A : Matrix R C ℤ) (w : R → ℤ)
    (hi : LinearIndependent ℚ (fun c => fun r => (A r c:ℚ)))
    (hc : (fun r => (w r:ℚ)) ∈ Submodule.span ℚ (Set.range (fun c => fun r => (A r c:ℚ)))) :
    let B := A.transpose*A
    let z := B.cramer (A.transpose*ᵥw)
    ∀ r, (A*ᵥz) r=B.det*w r := by
  let AQ : Matrix R C ℚ := fun r c => A r c
  have hc' : (fun r => (w r:ℚ)) ∈ LinearMap.range AQ.mulVecLin := by
    rwa [Matrix.range_mulVecLin]
  obtain ⟨x,hx⟩ := hc'
  change AQ*ᵥx=(fun r => (w r:ℚ)) at hx
  let B := A.transpose*A
  let z := B.cramer (A.transpose*ᵥw)
  have hz := Matrix.mulVec_cramer B (A.transpose*ᵥw)
  have hdet : B.det ≠ 0 := gram_det_ne_zero A hi
  have hB : Function.Injective ((fun c d => (B c d:ℚ))*ᵥ ·) := by
    apply Matrix.mulVec_injective_iff_isUnit.mpr
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    change IsUnit (((Int.castRingHom ℚ).mapMatrix B).det)
    rw [← RingHom.map_det (Int.castRingHom ℚ)]
    apply isUnit_iff_ne_zero.mpr
    change (B.det:ℚ) ≠ 0
    exact_mod_cast hdet
  have hBcast : (fun c d => (B c d:ℚ))=AQ.transpose*AQ := by
    exact Matrix.map_mul (L:=A.transpose) (M:=A) (f:=Int.castRingHom ℚ)
  have hzQ : (AQ.transpose*AQ)*ᵥ(fun c => (z c:ℚ))=(B.det:ℚ) •
      (AQ.transpose*ᵥ(fun r => (w r:ℚ))) := by
    rw [← hBcast]
    ext c
    have hh := congrFun hz c
    simp only [mulVec,dotProduct,Pi.smul_apply,smul_eq_mul] at hh ⊢
    change (∑ d, (B c d:ℚ)*(z d:ℚ))=(B.det:ℚ)*∑ r, (A r c:ℚ)*(w r:ℚ)
    change (∑ d, B c d*z d)=B.det*∑ r, A r c*w r at hh
    exact_mod_cast hh
  have he : (fun c => (z c:ℚ))=(B.det:ℚ) • x := by
    apply hB
    change ((fun c d => (B c d:ℚ))*ᵥ(fun c => (z c:ℚ))) =
      (fun c d => (B c d:ℚ))*ᵥ((B.det:ℚ) • x)
    rw [hBcast,hzQ,mulVec_smul,← mulVec_mulVec,hx]
  change ∀ r, (A*ᵥz) r=B.det*w r
  intro r
  have heq : (AQ*ᵥ(fun c => (z c:ℚ))) r=(B.det:ℚ)*(w r:ℚ) := by
    rw [he,mulVec_smul,hx]
    rfl
  simp only [mulVec,dotProduct,AQ] at heq ⊢
  exact_mod_cast heq

end MetricKMedian.Compression

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.GramBounds -/
section
namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix
variable {R C : Type} [Fintype R] [Fintype C] [DecidableEq C]

omit [Fintype C] [DecidableEq C] in
                                                                      
theorem gram_entry_bound (A : Matrix R C ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (c d : C) :
    |(A.transpose*A) c d| ≤ (Fintype.card R:ℤ)*M^2 := by
  rw [Matrix.mul_apply]
  calc
    _ ≤ ∑ r, |A r c*A r d| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : R, M^2 := sum_le_sum (fun r _ => by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hA r c) (hA r d) (abs_nonneg _) hM)
    _ = _ := by simp

omit [Fintype C] [DecidableEq C] in
theorem gram_rhs_bound (A : Matrix R C ℤ) (w : R → ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (hw : ∀ r, |w r| ≤ M) (c : C) :
    |(A.transpose*ᵥw) c| ≤ (Fintype.card R:ℤ)*M^2 := by
  change |∑ r, A r c*w r| ≤ _
  calc
    _ ≤ ∑ r, |A r c*w r| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _r : R, M^2 := sum_le_sum (fun r _ => by
      rw [abs_mul,pow_two]
      exact mul_le_mul (hA r c) (hw r) (abs_nonneg _) hM)
    _ = _ := by simp

theorem gram_det_bound (A : Matrix R C ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) :
    |(A.transpose*A).det| ≤ (Nat.factorial (Fintype.card C):ℤ)*
      ((Fintype.card R:ℤ)*M^2)^(Fintype.card C) := by
  simpa only [AbsoluteValue.abs_apply,nsmul_eq_mul] using
    (Matrix.det_le (abv := AbsoluteValue.abs) (gram_entry_bound A M hM hA))

theorem gram_cramer_bound (A : Matrix R C ℤ) (w : R → ℤ) (M : ℤ) (hM : 0 ≤ M)
    (hA : ∀ r c, |A r c| ≤ M) (hw : ∀ r, |w r| ≤ M) (c : C) :
    |((A.transpose*A).cramer (A.transpose*ᵥw)) c| ≤ (Nat.factorial (Fintype.card C):ℤ)*
      ((Fintype.card R:ℤ)*M^2)^(Fintype.card C) := by
  rw [Matrix.cramer_apply]
  have hentry : ∀ i j, |((A.transpose*A).updateCol c (A.transpose*ᵥw)) i j| ≤
      (Fintype.card R:ℤ)*M^2 := by
    intro i j
    by_cases hj : j=c
    · subst j
      simpa using gram_rhs_bound A w M hM hA hw i
    · simpa [Matrix.updateCol_apply,hj] using gram_entry_bound A M hM hA i j
  simpa only [AbsoluteValue.abs_apply,nsmul_eq_mul] using
    (Matrix.det_le (abv := AbsoluteValue.abs) hentry)

end MetricKMedian.Compression

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.IntegerCoefficientBounds -/
section
namespace OAI

namespace MetricKMedian.Compression

theorem gram_coefficient_bit_bound (r n L : ℕ) (hn : n ≤ r) :
    (n.factorial:ℤ)*((r:ℤ)*((2:ℤ)^L)^2)^n ≤ (2:ℤ)^(2*r*(r+L)) := by
  have hnr : n ≤ 2^r := hn.trans Nat.lt_two_pow_self.le
  have hf : n.factorial ≤ 2^(r*r) := by
    calc
      _ ≤ n^n := Nat.factorial_le_pow n
      _ ≤ (2^r)^n := Nat.pow_le_pow_left hnr n
      _ = 2^(r*n) := (pow_mul _ _ _).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_left r hn)
  have hfZ : (n.factorial:ℤ) ≤ 2^(r*r) := by exact_mod_cast hf
  have hrZ : (r:ℤ) ≤ 2^r := by exact_mod_cast (Nat.lt_two_pow_self (n:=r)).le
  have hb : (r:ℤ)*((2:ℤ)^L)^2 ≤ 2^(r+2*L) := by
    calc
      _ ≤ 2^r*((2:ℤ)^L)^2 := mul_le_mul_of_nonneg_right hrZ (sq_nonneg _)
      _ = _ := by rw [pow_add,Nat.mul_comm 2 L,pow_mul]
  have hbn : ((r:ℤ)*((2:ℤ)^L)^2)^n ≤ 2^((r+2*L)*r) := by
    calc
      _ ≤ ((2:ℤ)^(r+2*L))^n := pow_le_pow_left₀ (by positivity) hb n
      _ = 2^((r+2*L)*n) := (pow_mul _ _ _).symm
      _ ≤ _ := pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_left _ hn)
  calc
    _ ≤ 2^(r*r)*(2:ℤ)^((r+2*L)*r) :=
      mul_le_mul hfZ hbn (by positivity) (by positivity)
    _ = _ := by rw [← pow_add]; congr 1; ring

end MetricKMedian.Compression

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.DependentIntegerKernel -/
section
namespace OAI

namespace MetricKMedian.Compression
open Finset Matrix

theorem small_integer_dependence_of_dependent {R Ω : Type} [Fintype R] [Fintype Ω]
    (V : Matrix R Ω ℤ) (L : ℕ) (hV : ∀ r i, |V r i| ≤ (2:ℤ)^L)
    (hdep : ¬ LinearIndependent ℚ (fun i r => (V r i:ℚ))) :
    ∃ (K : Type) (inst : Fintype K), letI := inst;
      ∃ (a : K → Ω) (z : K → ℤ), Function.Injective a ∧
        Fintype.card K ≤ Fintype.card R+1 ∧ (∃ k, z k ≠ 0) ∧
        (∀ k, |z k| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L))) ∧
        ∀ r, ∑ k, z k*V r (a k)=0 := by
  classical
  let v : Ω → R → ℚ := fun i r => V r i
  obtain ⟨κ,a,ha,hspan,hi⟩ := exists_linearIndependent' ℚ v
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card κ ≤ Fintype.card R := by
    simpa using hi.fintype_card_le_finrank
  have hns : ¬ Function.Surjective a := by
    intro hs
    apply hdep
    let e := Equiv.ofBijective a ⟨ha,hs⟩
    have hh := hi.comp e.symm e.symm.injective
    have he : (v ∘ a) ∘ e.symm=v := by
      funext i
      change v (e (e.symm i))=v i
      rw [e.apply_symm_apply]
    rw [he] at hh
    exact hh
  simp only [Function.Surjective,not_forall,not_exists] at hns
  obtain ⟨w,hw⟩ := hns
  let A : Matrix R κ ℤ := fun r c => V r (a c)
  let wv : R → ℤ := fun r => V r w
  let B := A.transpose*A
  let D := B.det
  let b := B.cramer (A.transpose*ᵥwv)
  have hAi : LinearIndependent ℚ (fun c r => (A r c:ℚ)) := hi
  have hwm : (fun r => (wv r:ℚ)) ∈ Submodule.span ℚ (Set.range (fun c r => (A r c:ℚ))) := by
    change v w ∈ Submodule.span ℚ (Set.range (v ∘ a))
    rw [hspan]
    exact Submodule.subset_span (Set.mem_range_self w)
  have hD : D ≠ 0 := gram_det_ne_zero A hAi
  have heq : ∀ r, (A*ᵥb) r=D*wv r := gram_span_relation A wv hAi hwm
  have hbnd := gram_coefficient_bit_bound (Fintype.card R) (Fintype.card κ) L hcard
  have hAb : ∀ r c, |A r c| ≤ (2:ℤ)^L := fun r c => hV r (a c)
  have hwv : ∀ r, |wv r| ≤ (2:ℤ)^L := fun r => hV r w
  have hDb : |D| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L)) :=
    (gram_det_bound A _ (by positivity) hAb).trans hbnd
  have hbb : ∀ c, |b c| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L)) :=
    fun c => (gram_cramer_bound A wv _ (by positivity) hAb hwv c).trans hbnd
  let a' : Option κ → Ω := fun k => k.elim w a
  let z : Option κ → ℤ := fun k => k.elim D (fun c => -b c)
  refine ⟨Option κ,inferInstance,a',z,?_,?_,⟨none,hD⟩,?_,?_⟩
  · intro c d he
    cases c with
    | none =>
      cases d with
      | none => rfl
      | some d => exact False.elim (hw d he.symm)
    | some c =>
      cases d with
      | none => exact False.elim (hw c he)
      | some d => exact congrArg some (ha he)
  · simp only [Fintype.card_option]
    omega
  · intro k
    cases k with
    | none => exact hDb
    | some c => simpa only [z,Option.elim_some,abs_neg] using hbb c
  · intro r
    rw [Fintype.sum_option]
    change D*wv r+(∑ c, (-b c)*A r c)=0
    have hh := heq r
    change (∑ c, A r c*b c)=D*wv r at hh
    simp only [neg_mul,sum_neg_distrib,mul_comm (b _) (A _ _)]
    rw [hh]
    ring

theorem full_integer_kernel_of_dependent {R Ω : Type} [Fintype R] [Fintype Ω]
    (V : Matrix R Ω ℤ) (L : ℕ) (hV : ∀ r i, |V r i| ≤ (2:ℤ)^L)
    (hdep : ¬ LinearIndependent ℚ (fun i r => (V r i:ℚ))) :
    ∃ z : Ω → ℤ, (∃ i, z i ≠ 0) ∧
      (∀ i, |z i| ≤ (2:ℤ)^(2*Fintype.card R*(Fintype.card R+L))) ∧
      ∀ r, ∑ i, z i*V r i=0 := by
  classical
  obtain ⟨K,inst,a,z,ha,_,hne,hbound,hker⟩ := small_integer_dependence_of_dependent V L hV hdep
  let zz : Ω → ℤ := fun i => ∑ k, if a k=i then z k else 0
  have hzval : ∀ k, zz (a k)=z k := by
    intro k
    simp only [zz,ha.eq_iff]
    simpa only [mem_univ,ite_true] using sum_ite_eq' univ k z
  have hzout : ∀ i, (¬∃ k, a k=i) → zz i=0 := by
    intro i hi
    apply sum_eq_zero
    intro k _
    exact if_neg (fun hk => hi ⟨k,hk⟩)
  refine ⟨zz,?_,?_,?_⟩
  · obtain ⟨k,hk⟩ := hne
    exact ⟨a k,by rwa [hzval]⟩
  · intro i
    by_cases hi : ∃ k, a k=i
    · obtain ⟨k,rfl⟩ := hi
      rw [hzval]
      exact hbound k
    · rw [hzout i hi,abs_zero]
      positivity
  · intro r
    change (∑ i, (∑ k, if a k=i then z k else 0)*V r i)=0
    simp only [sum_mul,ite_mul,zero_mul]
    rw [sum_comm]
    simpa using hker r

end MetricKMedian.Compression

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.CircuitBitBound -/
section
namespace OAI

namespace MetricKMedian.Gaussian
open Finset

theorem circuit_integer_ratio {r n : ℕ} (V : Fin r → Fin n → ℤ)
    (z : Fin n → ℚ) (L : ℕ) (hV : ∀ i j, |V i j| ≤ (2:ℤ)^L)
    (hz : ∀ i, ∑ j, (V i j:ℚ)*z j=0)
    (hc : IsCircuit (fun i j => (V i j:ℚ)) z) (w : Fin n) (hw : z w=1) :
    ∃ U : Fin n → ℤ, U w ≠ 0 ∧
      (∀ j, |U j| ≤ (2:ℤ)^(2*r*(r+L))) ∧
      ∀ j, z j=(U j:ℚ)/(U w:ℚ) := by
  classical
  let S := univ.filter (fun j => z j ≠ 0)
  have hwS : w ∈ S := by simp only [S,mem_filter,mem_univ,true_and,hw,ne_eq,one_ne_zero,not_false_eq_true]
  have hdep : ¬ LinearIndependent ℚ (fun j : ↥S => fun i => (V i j.val:ℚ)) := by
    intro hi
    have hsum : ∑ j : ↥S, z j.val • (fun i => (V i j.val:ℚ))=0 := by
      funext i
      simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Pi.zero_apply]
      rw [sum_coe_sort S (fun j => z j*(V i j:ℚ))]
      have he : (∑ j ∈ S, z j*(V i j:ℚ))=∑ j, z j*(V i j:ℚ) := by
        apply sum_subset (subset_univ _)
        intro j _ hj
        have he : z j=0 := by simpa only [S,mem_filter,mem_univ,true_and,not_not] using hj
        rw [he,zero_mul]
      rw [he]
      simpa only [mul_comm] using hz i
    have hh := (Fintype.linearIndependent_iff.mp hi) (fun j => z j.val) hsum ⟨w,hwS⟩
    rw [hw] at hh
    exact one_ne_zero hh
  obtain ⟨u,hune,hb,hker⟩ := Compression.full_integer_kernel_of_dependent
    (fun i (j : ↥S) => V i j.val) L (fun i j => hV i j.val) hdep
  let U : Fin n → ℤ := fun j => if h : j ∈ S then u ⟨j,h⟩ else 0
  have hUval : ∀ j : ↥S, U j.val=u j := by intro j; simp only [U,dif_pos j.property]
  have hUne : ∃ j, U j ≠ 0 := by
    obtain ⟨j,hj⟩ := hune
    exact ⟨j.val,by rwa [hUval]⟩
  have hUz : ∀ j, z j=0 → U j=0 := by
    intro j hj
    have hn : j ∉ S := by simp only [S,mem_filter,mem_univ,true_and,hj,ne_eq,not_true_eq_false,not_false_eq_true]
    exact dif_neg hn
  have hUker : ∀ i, ∑ j, (V i j:ℚ)*(U j:ℚ)=0 := by
    intro i
    have hh : (∑ j, U j*V i j)=∑ j : ↥S, u j*V i j.val := by
      calc
        _ = ∑ j ∈ S, U j*V i j := by
          symm
          apply sum_subset (subset_univ _)
          intro j _ hj
          simp only [U,dif_neg hj,zero_mul]
        _ = _ := by rw [← sum_coe_sort]; exact sum_congr rfl (fun j _ => by rw [hUval])
    have hh' := hh.trans (hker i)
    have hcast : (∑ j, (U j:ℚ)*(V i j:ℚ))=0 := by exact_mod_cast hh'
    simpa only [mul_comm] using hcast
  obtain ⟨t,ht⟩ := hc (fun j => (U j:ℚ)) (by intro j hj; exact_mod_cast hUz j hj) hUker
  have htw : (U w:ℚ)=t := by simpa only [hw,mul_one] using ht w
  have htn : t ≠ 0 := by
    intro ht0
    obtain ⟨j,hj⟩ := hUne
    have hh := ht j
    rw [ht0,zero_mul] at hh
    exact hj (by exact_mod_cast hh)
  have hUw : U w ≠ 0 := by intro hn; simp only [hn,Int.cast_zero] at htw; exact htn htw.symm
  refine ⟨U,hUw,?_,?_⟩
  · intro j
    by_cases hj : j ∈ S
    · rw [show U j=u ⟨j,hj⟩ from dif_pos hj]
      simpa only [Fintype.card_fin] using hb ⟨j,hj⟩
    · rw [show U j=0 from dif_neg hj,abs_zero]; positivity
  · intro j
    rw [htw]
    apply (eq_div_iff htn).mpr
    rw [ht j]
    ring

theorem ratio_num_den_bound (a b : ℤ) (hb : b ≠ 0) (H : ℤ)
    (ha : |a| ≤ H) (hbH : |b| ≤ H) :
    |((a:ℚ)/(b:ℚ)).num| ≤ H ∧ (((a:ℚ)/(b:ℚ)).den:ℤ) ≤ H := by
  let q := (a:ℚ)/(b:ℚ)
  obtain ⟨c,hcA,hcB⟩ := Rat.num_den_mk hb (q := q) (by exact (Rat.divInt_eq_div a b).symm)
  have hc : c ≠ 0 := by intro hz; rw [hz,zero_mul] at hcB; exact hb hcB
  have hc1 : (1:ℤ) ≤ |c| := by
    have ha := abs_pos.mpr hc
    omega
  have hnum : |q.num| ≤ |a| := by
    rw [hcA,abs_mul]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (abs_nonneg q.num)
  have hden : (q.den:ℤ) ≤ |b| := by
    rw [hcB,abs_mul,abs_of_nonneg (by positivity : (0:ℤ) ≤ q.den)]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hc1 (Int.natCast_nonneg q.den)
  exact ⟨hnum.trans ha,hden.trans hbH⟩

theorem integer_input_kernel_bounds (r n L : ℕ) (V : Fin r → Fin n → ℤ)
    (hn : r < n) (hV : ∀ i j, |V i j| ≤ (2:ℤ)^L) :
    let z := kernel r n (fun i j => (V i j:ℚ))
    ∀ j, |(z j).num| ≤ (2:ℤ)^(2*r*(r+L)) ∧
      ((z j).den:ℤ) ≤ (2:ℤ)^(2*r*(r+L)) := by
  dsimp only
  obtain ⟨⟨w,hw⟩,hc⟩ := kernel_circuit r n (fun i j => (V i j:ℚ)) hn
  have hk := (kernel_spec r n (fun i j => (V i j:ℚ)) hn).2
  obtain ⟨U,hUw,hU,hz⟩ := circuit_integer_ratio V _ L hV hk hc w hw
  intro j
  rw [hz j]
  exact ratio_num_den_bound (U j) (U w) hUw _ (hU j) (hU w)

end MetricKMedian.Gaussian

end OAI
end

/- OAI.Combinatorics.KMedian.Compression.RationalOperationHeight -/
section
namespace OAI


                                               
section
namespace MetricKMedian.Binary
open Finset

def HasHeight (q : ℚ) (L : ℕ) : Prop := |q.num| ≤ (2:ℤ)^L ∧ (q.den:ℤ) ≤ (2:ℤ)^L

namespace HasHeight
variable {q r : ℚ} {L M : ℕ}

 theorem mono (h : HasHeight q L) (hLM : L≤M) : HasHeight q M :=
  ⟨h.1.trans (pow_le_pow_right₀ (by norm_num) hLM),h.2.trans (pow_le_pow_right₀ (by norm_num) hLM)⟩

 theorem zero (L : ℕ) : HasHeight 0 L := by
  constructor
  · simp
  · simp only [Rat.den_zero,Int.natCast_one]
    exact one_le_pow₀ (by norm_num)

 theorem one (L : ℕ) : HasHeight 1 L := by
  constructor <;> simp only [Rat.num_one,Rat.den_one,abs_one,Int.natCast_one] <;>
    exact one_le_pow₀ (by norm_num)

 theorem neg (h : HasHeight q L) : HasHeight (-q) L := by
  simpa only [HasHeight,Rat.num_neg_eq_neg_num,Rat.den_neg_eq_den,abs_neg] using h

 theorem mul (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q*r) (L+M) := by
  have hdq : (q.den:ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hdr : (r.den:ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hh := Gaussian.ratio_num_den_bound (q.num*r.num) ((q.den:ℤ)*r.den) (mul_ne_zero hdq hdr)
    ((2:ℤ)^(L+M)) (by
      rw [abs_mul,pow_add]
      exact mul_le_mul hq.1 hr.1 (abs_nonneg _) (by positivity)) (by
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _),pow_add]
      exact mul_le_mul hq.2 hr.2 (by positivity) (by positivity))
  have he : ((q.num*r.num:ℤ):ℚ)/(((q.den:ℤ)*r.den:ℤ):ℚ)=q*r := by
    push_cast
    rw [mul_div_mul_comm,Rat.num_div_den,Rat.num_div_den]
  rwa [he] at hh

 theorem inv (hq : HasHeight q L) : HasHeight q⁻¹ L := by
  by_cases hq0 : q=0
  · rw [hq0,inv_zero]
    exact zero L
  have hqn : q.num ≠ 0 := by
    intro h
    apply hq0
    rw [← Rat.num_div_den q,h,Int.cast_zero,zero_div]
  have hh := Gaussian.ratio_num_den_bound (q.den:ℤ) q.num hqn ((2:ℤ)^L)
    (by simpa only [abs_of_nonneg (Int.natCast_nonneg _)] using hq.2) hq.1
  have he : ((q.den:ℤ):ℚ)/(q.num:ℚ)=q⁻¹ := by
    conv_rhs => rw [← Rat.num_div_den q]
    simp only [inv_div,Int.cast_natCast]
  rwa [he] at hh

 theorem div (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q/r) (L+M) := by
  simpa only [div_eq_mul_inv] using hq.mul hr.inv

 theorem add (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q+r) (L+M+1) := by
  have hdq : (q.den:ℤ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hdr : (r.den:ℤ) ≠ 0 := by exact_mod_cast r.den_ne_zero
  have hterm₁ : |q.num*(r.den:ℤ)| ≤ (2:ℤ)^(L+M) := by
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),pow_add]
    exact mul_le_mul hq.1 hr.2 (by positivity) (by positivity)
  have hterm₂ : |r.num*(q.den:ℤ)| ≤ (2:ℤ)^(L+M) := by
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),Nat.add_comm L M,pow_add]
    exact mul_le_mul hr.1 hq.2 (by positivity) (by positivity)
  have hh := Gaussian.ratio_num_den_bound (q.num*r.den+r.num*q.den) ((q.den:ℤ)*r.den)
    (mul_ne_zero hdq hdr) ((2:ℤ)^(L+M+1)) (by
      have hab := abs_add_le (q.num*(r.den:ℤ)) (r.num*(q.den:ℤ))
      rw [pow_succ]
      linarith) (by
      rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg _),abs_of_nonneg (Int.natCast_nonneg _)]
      have hb : (q.den:ℤ)*r.den ≤ (2:ℤ)^(L+M) := by
        rw [pow_add]
        exact mul_le_mul hq.2 hr.2 (by positivity) (by positivity)
      exact hb.trans (pow_le_pow_right₀ (by norm_num) (by omega)))
  have he : ((q.num*r.den+r.num*q.den:ℤ):ℚ)/(((q.den:ℤ)*r.den:ℤ):ℚ)=q+r := by
    push_cast
    rw [add_div, mul_div_mul_right _ _ (Nat.cast_ne_zero.mpr r.den_ne_zero),
      mul_comm (r.num:ℚ) (q.den:ℚ),mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr q.den_ne_zero),
      Rat.num_div_den,Rat.num_div_den]
  rwa [he] at hh

 theorem sub (hq : HasHeight q L) (hr : HasHeight r M) : HasHeight (q-r) (L+M+1) := by
  simpa only [sub_eq_add_neg] using hq.add hr.neg

 theorem sum {ι : Type*} (s : Finset ι) (f : ι → ℚ) (h : ∀ i∈s, HasHeight (f i) L) :
    HasHeight (∑ i∈s, f i) (s.card*(L+1)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [sum_empty,card_empty,zero_mul] using zero 0
  | @insert a s ha ih =>
      rw [sum_insert ha,card_insert_of_notMem ha]
      have hs := ih (fun i hi => h i (mem_insert_of_mem hi))
      have hh := (h a (mem_insert_self _ _)).add hs
      convert hh using 1
      ring

 theorem partialSum {n : ℕ} (f : Fin n → ℚ) (s : Finset (Fin n))
    (h : ∀ i, HasHeight (f i) L) : HasHeight (∑ i∈s, f i) (n*(L+1)) := by
  have hh := sum s f (fun i _ => h i)
  apply hh.mono
  exact Nat.mul_le_mul_right _ ((card_le_card (subset_univ s)).trans_eq (card_fin n))

end HasHeight
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryRationalHeight -/
section
namespace OAI


                                            
section
namespace MetricKMedian.Binary
open Polynomial
namespace NatBinary
 theorem length_le_height {n L : ℕ} (h : n ≤ 2^L) : n.bits.length ≤ L+1 := by
  rw [Nat.size_eq_bits_len]
  apply Nat.size_le.mpr
  have hp : 0<2^L := pow_pos (by decide) _
  rw [pow_succ]
  omega
 theorem le_two_pow_length (n : ℕ) : n ≤ 2^n.bits.length := by
  simpa only [Nat.size_eq_bits_len] using (Nat.lt_size_self n).le
end NatBinary

namespace Signed
 theorem encode_length (z : ℤ) : (encode z).length=3+z.natAbs.bits.length := by
  simp only [encode,parts,encodePair_length,encodeBool,List.length_singleton]

 theorem encode_injective : Function.Injective encode := by
  intro a b h
  have hh := encodePair_injective encodeBool_injective (fun n m he => by
    have hg := congrArg Word.value he
    simpa only [Word.value_bits] using hg) h
  have hx := congrArg (fun x : Bool × ℕ => value x.1 x.2) hh
  simpa only [parts,value_parts] using hx
end Signed
namespace Ratio
 theorem encode_length (q : ℚ) : (encode q).length=7+2*q.num.natAbs.bits.length+q.den.bits.length := by
  simp only [encode,parts,encodePair_length,Signed.encode_length]
  omega
 theorem encode_injective : Function.Injective encode := by
  intro a b h
  have hh := encodePair_injective Signed.encode_injective (fun n m he => by
    have hg := congrArg Word.value he
    simpa only [Word.value_bits] using hg) h
  have hn := congrArg Prod.fst hh
  have hd := congrArg Prod.snd hh
  exact Rat.ext hn hd
 theorem height_length (q : ℚ) : HasHeight q (encode q).length := by
  have hn := NatBinary.le_two_pow_length q.num.natAbs
  have hd := NatBinary.le_two_pow_length q.den
  have hlen := encode_length q
  have hnb : q.num.natAbs.bits.length ≤ (encode q).length := by omega
  have hdb : q.den.bits.length ≤ (encode q).length := by omega
  have hN := hn.trans (Nat.pow_le_pow_right (by decide : 1≤2) hnb)
  have hD := hd.trans (Nat.pow_le_pow_right (by decide : 1≤2) hdb)
  constructor
  · simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using (Nat.cast_le (α:=ℤ)).mpr hN
  · simpa only [Nat.cast_pow,Nat.cast_ofNat] using (Nat.cast_le (α:=ℤ)).mpr hD
 theorem length_height {q : ℚ} {L : ℕ} (h : HasHeight q L) : (encode q).length ≤ 3*L+10 := by
  have hN : q.num.natAbs ≤ 2^L := (Nat.cast_le (α:=ℤ)).mp (by
    simpa only [Nat.cast_pow,Nat.cast_ofNat,Int.natCast_natAbs] using h.1)
  have hD : q.den ≤ 2^L := (Nat.cast_le (α:=ℤ)).mp (by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using h.2)
  have hnb := NatBinary.length_le_height hN
  have hdb := NatBinary.length_le_height hD
  rw [encode_length]
  omega
end Ratio
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListIndices -/
section
namespace OAI


                                         
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListAlgorithms
variable {α : Type}
def indexStep (x : (ℕ × List ℕ) × α) : ℕ × List ℕ := (x.1.1+1,x.1.1::x.1.2)
 theorem pushIndices (xs : List α) (n : ℕ) (bs : List ℕ) :
    xs.foldl (fun b a => indexStep (b,a)) (n,bs)=
      (n+xs.length,(List.range' n xs.length).reverse++bs) := by
  induction xs generalizing n bs with
  | nil => simp
  | cons a xs ih =>
      change xs.foldl (fun b a => indexStep (b,a)) (n+1,n::bs)=_
      rw [ih]
      simp only [List.length_cons,List.range'_succ,List.reverse_cons,List.append_assoc,List.singleton_append]
      congr 1
      omega
 theorem index_partial_size (ea : α → List Bool) (xs : List α) (x : ℕ × List ℕ) (pre suf : List α)
    (he : xs=pre++suf) :
    (encodePair Nat.bits (encodeList Nat.bits) (pre.foldl (fun b a => indexStep (b,a)) x)).length ≤
      10*((encodePair (encodeList ea) (encodePair Nat.bits (encodeList Nat.bits)) (xs,x)).length+1)^2 := by
  let L := (encodePair (encodeList ea) (encodePair Nat.bits (encodeList Nat.bits)) (xs,x)).length
  have hp : pre.length ≤ L := by
    have hp : (encodeList ea pre).length ≤ (encodeList ea xs).length := by rw [he,EncodedList.append,List.length_append]; omega
    have hh := EncodedList.length_le ea pre
    simp only [L,encodePair_length]; omega
  have hn : x.1.bits.length ≤ L := by simp only [L,encodePair_length]; omega
  have hb : (encodeList Nat.bits x.2).length ≤ L := by simp only [L,encodePair_length]; omega
  have hl : pre.length.bits.length ≤ pre.length+1 := NatBinary.length_le_height (Nat.lt_two_pow_self.le)
  have hc := NatBinary.add_length x.1 pre.length
  have hi : ∀ q∈List.range' x.1 pre.length, q.bits.length ≤ 2*L+2 := by
    intro q hq
    have hq' : q ≤ x.1+pre.length := (List.mem_range'_1.mp hq).2.le
    have hh := (NatBinary.length_mono hq').trans hc
    omega
  have hr := EncodedList.length_bound Nat.bits (List.range' x.1 pre.length) (2*L+2) hi
  simp only [List.length_range'] at hr
  have hcount : (x.1+pre.length).bits.length ≤ 2*L+2 := by omega
  have hr' : (encodeList Nat.bits (List.range' x.1 pre.length)).length ≤ L*(4*L+5) := by
    calc
      _ ≤ pre.length*(2*(2*L+2)+1) := hr
      _ ≤ L*(2*(2*L+2)+1) := Nat.mul_le_mul_right _ hp
      _ = L*(4*L+5) := by ring
  change (encodePair Nat.bits (encodeList Nat.bits) (pre.foldl (fun b a => indexStep (b,a)) (x.1,x.2))).length ≤ _
  rw [pushIndices]
  simp only [encodePair_length,EncodedList.append,List.length_append,EncodedList.reverse_length]
  simp only [L,encodePair_length] at hcount hr' hb
  nlinarith

end ListAlgorithms
namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listIndices : PolyProgram (encodeList ea) (encodeList Nat.bits) (fun xs : List α => List.range xs.length) := by
  let eb := encodePair Nat.bits (encodeList Nat.bits)
  let acc := fst eb ea
  let n := acc.comp (fst Nat.bits (encodeList Nat.bits))
  let bs := acc.comp (snd Nat.bits (encodeList Nat.bits))
  let inc := (n.fanout (constant (encodePair eb ea) Nat.bits 1)).comp natAdd
  let push := (n.fanout bs).comp (listCons Nat.bits)
  let step : PolyProgram (encodePair eb ea) eb ListAlgorithms.indexStep :=
    (inc.fanout push).congr _ (fun _ => rfl)
  let fold := step.listFold a0 (10*(X+1)^2) (by
    intro xs x pre suf he
    simpa only [eval_mul,eval_ofNat,eval_pow,eval_add,eval_X,eval_one] using ListAlgorithms.index_partial_size ea xs x pre suf he)
  let start := (identity (encodeList ea)).fanout (constant (encodeList ea) eb (0,[]))
  exact ((((start.comp fold).comp (snd Nat.bits (encodeList Nat.bits))).comp (listReverse Nat.bits 0))).congr _ (fun xs => by
    simp only [Function.comp_apply,id_eq,ListAlgorithms.pushIndices,List.append_nil,List.reverse_reverse,← List.range_eq_range'])
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListIndex -/
section
namespace OAI


                                       
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListSplit
variable {α : Type} (ea : α → List Bool) (a0 : α)
abbrev enc : List α × (ℕ × List α) → List Bool := encodePair (encodeList ea) (encodePair Nat.bits (encodeList ea))
abbrev out : List α × List α → List Bool := encodePair (encodeList ea) (encodeList ea)
def body (x : List α × (ℕ × List α)) : (List α × List α) ⊕ (List α × (ℕ × List α)) :=
  if x.1.isEmpty || decide (x.2.1=0) then .inl (x.2.2.reverse,x.1)
  else .inr (x.1.tail,(x.2.1-1,x.1.head?.getD a0::x.2.2))
def result (x : List α × (ℕ × List α)) : List α × List α := (x.2.2.reverse++x.1.take x.2.1,x.1.drop x.2.1)
noncomputable def program : PolyProgram (enc ea) (encodeLoop (enc ea) (out ea)) (body a0) := by
  let ls := PolyProgram.fst (encodeList ea) (encodePair Nat.bits (encodeList ea))
  let ns := PolyProgram.snd (encodeList ea) (encodePair Nat.bits (encodeList ea))
  let n := ns.comp (PolyProgram.fst Nat.bits (encodeList ea))
  let bs := ns.comp (PolyProgram.snd Nat.bits (encodeList ea))
  let zero := (((ls.comp (PolyProgram.listIsEmpty ea)).fanout (n.comp PolyProgram.natZero)).comp PolyProgram.boolOr)
  let done := (((bs.comp (PolyProgram.listReverse ea a0)).fanout ls).comp (PolyProgram.injectLeft (enc ea) (out ea)))
  let pred := ((n.fanout (PolyProgram.constant (enc ea) Nat.bits 1)).comp PolyProgram.natSub)
  let push := (((ls.comp (PolyProgram.listHead ea a0)).fanout bs).comp (PolyProgram.listCons ea))
  let cont := (((ls.comp (PolyProgram.listTail ea a0)).fanout (pred.fanout push)).comp (PolyProgram.injectRight (enc ea) (out ea)))
  exact (PolyProgram.ite zero cont done).congr _ (fun _ => rfl)

 theorem run (as bs : List α) (n S : ℕ) (hsize : (enc ea (as,(n,bs))).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea) (body a0) S t (as,(n,bs)) (result (as,(n,bs))) := by
  induction as generalizing n bs with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp only [body,result,List.isEmpty_nil,Bool.true_or,List.take_nil,List.drop_nil,List.append_nil]
      rfl
  | cons a as ih =>
      cases n with
      | zero =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp only [body,result,List.isEmpty_cons,decide_true,Bool.false_or,List.take_zero,List.drop_zero,List.append_nil]
          rfl
      | succ n =>
          have hn := NatBinary.length_mono (Nat.le_succ n)
          change n.bits.length ≤ (n+1).bits.length at hn
          have hs : (enc ea (as,(n,a::bs))).length ≤ S := by
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih (a::bs) n hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have hb : body a0 (a::as,(n+1,bs))=.inr (as,(n,a::bs)) := by simp [body]
          have he : result (as,(n,a::bs))=result (a::as,(n+1,bs)) := by
            simp only [result,List.reverse_cons,List.take_succ_cons,List.drop_succ_cons,List.append_assoc,List.singleton_append]
          rw [← he]
          exact BoundedRun.step hsize hb hr

noncomputable def loop : PolyProgram (enc ea) (out ea) result :=
  (program ea a0).loop result (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea a0 x.1 x.2.2 x.2.1 (enc ea x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListSplit

namespace PolyProgram
variable {α : Type} (ea : α → List Bool) (a0 : α)
noncomputable def listSplitAt : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodePair (encodeList ea) (encodeList ea)) (fun x : List α × ℕ => (x.1.take x.2,x.1.drop x.2)) := by
  let ls := fst (encodeList ea) Nat.bits
  let n := snd (encodeList ea) Nat.bits
  let start := ls.fanout (n.fanout (constant (encodePair (encodeList ea) Nat.bits) (encodeList ea) []))
  exact (start.comp (ListSplit.loop ea a0)).congr _ (fun x => by simp only [Function.comp_apply,ListSplit.result,List.reverse_nil,List.nil_append])
noncomputable def listTake : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.take x.2) :=
  ((listSplitAt ea a0).comp (fst (encodeList ea) (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listDrop : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.drop x.2) :=
  ((listSplitAt ea a0).comp (snd (encodeList ea) (encodeList ea))).congr _ (fun _ => rfl)
noncomputable def listGetD : PolyProgram (encodePair (encodeList ea) Nat.bits)
    ea (fun x : List α × ℕ => x.1[x.2]?.getD a0) := by
  exact ((listDrop ea a0).comp (listHead ea a0)).congr _ (fun x => by
    simp only [Function.comp_apply,List.head?_drop])
noncomputable def listEraseIdx : PolyProgram (encodePair (encodeList ea) Nat.bits)
    (encodeList ea) (fun x : List α × ℕ => x.1.take x.2++(x.1.drop x.2).tail) :=
  (((listSplitAt ea a0).comp ((listTail ea a0).second (encodeList ea))).comp (listAppend ea a0)).congr _ (fun _ => rfl)
noncomputable def listInsertAt : PolyProgram (encodePair (encodePair (encodeList ea) Nat.bits) ea)
    (encodeList ea) (fun x : (List α × ℕ) × α => x.1.1.take x.1.2++x.2::x.1.1.drop x.1.2) := by
  let sp := (fst (encodePair (encodeList ea) Nat.bits) ea).comp (listSplitAt ea a0)
  let pre := sp.comp (fst (encodeList ea) (encodeList ea))
  let suf := sp.comp (snd (encodeList ea) (encodeList ea))
  let elem := snd (encodePair (encodeList ea) Nat.bits) ea
  exact ((pre.fanout ((elem.fanout suf).comp (listCons ea))).comp (listAppend ea a0)).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListZip -/
section
namespace OAI


                                     
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListZip
variable {α β : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α) (b0 : β)
abbrev enc : (List α × List β) × List (α × β) → List Bool :=
  encodePair (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
def body (x : (List α × List β) × List (α × β)) : List (α × β) ⊕ ((List α × List β) × List (α × β)) :=
  if x.1.1.isEmpty || x.1.2.isEmpty then .inl x.2.reverse
  else .inr ((x.1.1.tail,x.1.2.tail),(x.1.1.head?.getD a0,x.1.2.head?.getD b0)::x.2)
def result (x : (List α × List β) × List (α × β)) : List (α × β) := x.2.reverse++x.1.1.zip x.1.2
noncomputable def program : PolyProgram (enc ea eb) (encodeLoop (enc ea eb) (encodeList (encodePair ea eb))) (body a0 b0) := by
  let pair := PolyProgram.fst (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
  let as := pair.comp (PolyProgram.fst (encodeList ea) (encodeList eb))
  let bs := pair.comp (PolyProgram.snd (encodeList ea) (encodeList eb))
  let cs := PolyProgram.snd (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb))
  let test := (((as.comp (PolyProgram.listIsEmpty ea)).fanout (bs.comp (PolyProgram.listIsEmpty eb))).comp PolyProgram.boolOr)
  let done := ((cs.comp (PolyProgram.listReverse (encodePair ea eb) (a0,b0))).comp (PolyProgram.injectLeft (enc ea eb) (encodeList (encodePair ea eb))))
  let heads := (as.comp (PolyProgram.listHead ea a0)).fanout (bs.comp (PolyProgram.listHead eb b0))
  let tails := (as.comp (PolyProgram.listTail ea a0)).fanout (bs.comp (PolyProgram.listTail eb b0))
  let push := ((heads.fanout cs).comp (PolyProgram.listCons (encodePair ea eb)))
  let cont := ((tails.fanout push).comp (PolyProgram.injectRight (enc ea eb) (encodeList (encodePair ea eb))))
  exact (PolyProgram.ite test cont done).congr _ (fun _ => rfl)

 theorem run (as : List α) (bs : List β) (cs : List (α × β)) (S : ℕ)
    (hsize : (enc ea eb ((as,bs),cs)).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea eb) (body a0 b0) S t ((as,bs),cs) (result ((as,bs),cs)) := by
  induction as generalizing bs cs with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp [body,result]
  | cons a as ih =>
      cases bs with
      | nil =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp [body,result]
      | cons b bs =>
          have hs : (enc ea eb ((as,bs),(a,b)::cs)).length ≤ S := by
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih bs ((a,b)::cs) hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have he : result ((as,bs),(a,b)::cs)=result ((a::as,b::bs),cs) := by
            simp only [result,List.reverse_cons,List.zip_cons_cons,List.append_assoc,List.singleton_append]
          rw [← he]
          exact BoundedRun.step hsize (by simp [body]) hr

noncomputable def loop : PolyProgram (enc ea eb) (encodeList (encodePair ea eb)) result :=
  (program ea eb a0 b0).loop result (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea eb a0 b0 x.1.1 x.1.2 x.2 (enc ea eb x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListZip
namespace PolyProgram
variable {α β γ : Type} (ea : α → List Bool) (eb : β → List Bool) (a0 : α) (b0 : β)
noncomputable def listZip : PolyProgram (encodePair (encodeList ea) (encodeList eb))
    (encodeList (encodePair ea eb)) (fun x : List α × List β => x.1.zip x.2) := by
  let start := (identity (encodePair (encodeList ea) (encodeList eb))).fanout
    (constant (encodePair (encodeList ea) (encodeList eb)) (encodeList (encodePair ea eb)) [])
  exact (start.comp (ListZip.loop ea eb a0 b0)).congr _ (fun _ => by simp only [Function.comp_apply,id_eq,ListZip.result,List.reverse_nil,List.nil_append])
noncomputable def listZipWith {ec : γ → List Bool} {f : α × β → γ}
    (P : PolyProgram (encodePair ea eb) ec f) :
    PolyProgram (encodePair (encodeList ea) (encodeList eb)) (encodeList ec) (fun x : List α × List β => (x.1.zip x.2).map f) :=
  ((listZip ea eb a0 b0).comp (P.listMap (a0,b0))).congr _ (fun _ => rfl)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryPredicates -/
section
namespace OAI


                                        
section
namespace MetricKMedian.Binary.PolyProgram
noncomputable def natLE : PolyProgram (encodePair Nat.bits Nat.bits) encodeBool (fun x : ℕ × ℕ => decide (x.1≤x.2)) :=
  (((exchange Nat.bits Nat.bits).comp natLT).comp boolNot).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [Function.comp_def,h,not_lt.mpr h]
    · simp [Function.comp_def,h,lt_of_not_ge h])
noncomputable def natEQ : PolyProgram (encodePair Nat.bits Nat.bits) encodeBool (fun x : ℕ × ℕ => decide (x.1=x.2)) :=
  ((natLE.fanout ((exchange Nat.bits Nat.bits).comp natLE)).comp boolAnd).congr _ (fun x => by
    by_cases h₁ : x.1≤x.2 <;> by_cases h₂ : x.2≤x.1 <;> simp [Function.comp_apply,Prod.swap,h₁,h₂,le_antisymm_iff])
noncomputable def ratZero : PolyProgram Ratio.encode encodeBool (fun q => decide (q=0)) :=
  ((ratNum.comp intAbs).comp natZero).congr _ (fun q => by
    simp only [Function.comp_apply,Int.natAbs_eq_zero,Rat.num_eq_zero])
noncomputable def ratNonzero : PolyProgram Ratio.encode encodeBool (fun q => decide (q≠0)) :=
  (ratZero.comp boolNot).congr _ (fun q => by simp)
noncomputable def ratEQ : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1=x.2)) :=
  (ratSub.comp ratZero).congr _ (fun q => by simp only [Function.comp_apply,sub_eq_zero])
noncomputable def ratLE : PolyProgram (encodePair Ratio.encode Ratio.encode) encodeBool (fun x : ℚ × ℚ => decide (x.1≤x.2)) :=
  (((exchange Ratio.encode Ratio.encode).comp ratLT).comp boolNot).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [Function.comp_def,h,not_lt.mpr h]
    · simp [Function.comp_def,h,lt_of_not_ge h])
end MetricKMedian.Binary.PolyProgram
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryListSelection -/
section
namespace OAI


                                           
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace ListFindIdx
variable {α : Type} (ea : α → List Bool) (a0 : α) (p : α → Bool)
abbrev enc : List α × ℕ → List Bool := encodePair (encodeList ea) Nat.bits
def body (x : List α × ℕ) : ℕ ⊕ (List α × ℕ) :=
  if x.1.isEmpty || p (x.1.head?.getD a0) then .inl x.2 else .inr (x.1.tail,x.2+1)
def result (x : List α × ℕ) : ℕ := x.2+x.1.findIdx p
noncomputable def program (P : PolyProgram ea encodeBool p) :
    PolyProgram (enc ea) (encodeLoop (enc ea) Nat.bits) (body a0 p) := by
  let ls := PolyProgram.fst (encodeList ea) Nat.bits
  let n := PolyProgram.snd (encodeList ea) Nat.bits
  let hd := (ls.comp (PolyProgram.listHead ea a0)).comp P
  let test := ((ls.comp (PolyProgram.listIsEmpty ea)).fanout hd).comp PolyProgram.boolOr
  let done := n.comp (PolyProgram.injectLeft (enc ea) Nat.bits)
  let inc := (n.fanout (PolyProgram.constant (enc ea) Nat.bits 1)).comp PolyProgram.natAdd
  let cont := (((ls.comp (PolyProgram.listTail ea a0)).fanout inc).comp (PolyProgram.injectRight (enc ea) Nat.bits))
  exact (PolyProgram.ite test cont done).congr _ (fun _ => rfl)
 theorem run (as : List α) (n S : ℕ) (hsize : (enc ea (as,n)).length ≤ S) :
    ∃ t ≤ as.length+1, BoundedRun (enc ea) (body a0 p) S t (as,n) (result p (as,n)) := by
  induction as generalizing n with
  | nil =>
      refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
      simp [body,result]
  | cons a as ih =>
      cases hp : p a with
      | true =>
          refine ⟨1,by simp,BoundedRun.stop hsize ?_⟩
          simp [body,result,hp,List.findIdx_cons]
      | false =>
          have hn := NatBinary.add_length n 1
          have hs : (enc ea (as,n+1)).length ≤ S := by
            have hone : (1:ℕ).bits.length=1 := rfl
            rw [hone] at hn
            simp only [enc,encodePair_length,EncodedList.cons_length] at hsize ⊢
            omega
          obtain ⟨t,ht,hr⟩ := ih (n+1) hs
          refine ⟨t+1,by simpa only [List.length_cons] using Nat.succ_le_succ ht,?_⟩
          have he : result p (as,n+1)=result p (a::as,n) := by simp [result,List.findIdx_cons,hp,Nat.add_comm,Nat.add_left_comm]
          rw [← he]
          exact BoundedRun.step hsize (by simp [body,hp]) hr
noncomputable def loop (P : PolyProgram ea encodeBool p) : PolyProgram (enc ea) Nat.bits (result p) :=
  (program ea a0 p P).loop (result p) (X+1) X (fun x => by
    obtain ⟨t,ht,hr⟩ := run ea a0 p x.1 x.2 (enc ea x).length le_rfl
    refine ⟨t,?_,?_⟩
    · have hh := EncodedList.length_le ea x.1
      simp only [eval_add,eval_X,eval_one,enc,encodePair_length]
      omega
    · simpa only [eval_X] using hr)
end ListFindIdx
namespace ListAlgorithms
variable {α : Type}
 theorem foldChoice (p : α × α → Bool) (as : List α) (b : α) :
    as.foldl (fun b a => if p (b,a) then a else b) b=b ∨ as.foldl (fun b a => if p (b,a) then a else b) b∈as := by
  induction as generalizing b with
  | nil => exact Or.inl rfl
  | cons a as ih =>
      simp only [List.foldl_cons]
      cases hp : p (b,a)
      · simpa only [hp,Bool.false_eq_true,ite_false] using (ih b).imp_right (fun h => List.mem_cons_of_mem _ h)
      · simp only [ite_true]
        rcases ih a with he|hmem
        · exact Or.inr (by rw [he]; exact List.mem_cons_self)
        · exact Or.inr (List.mem_cons_of_mem _ hmem)
end ListAlgorithms
namespace PolyProgram
variable {α : Type} {ea : α → List Bool}
noncomputable def listFindIdx {p : α → Bool} (P : PolyProgram ea encodeBool p) (a0 : α) :
    PolyProgram (encodeList ea) Nat.bits (List.findIdx p) :=
  ((((identity (encodeList ea)).fanout (constant (encodeList ea) Nat.bits 0)).comp
    (ListFindIdx.loop ea a0 p P))).congr _ (fun _ => by simp only [Function.comp_apply,id_eq,ListFindIdx.result,Nat.zero_add])
noncomputable def listChoose {p : α × α → Bool} (P : PolyProgram (encodePair ea ea) encodeBool p) (a0 : α) :
    PolyProgram (encodePair (encodeList ea) ea) ea
      (fun x : List α × α => x.1.foldl (fun b a => if p (b,a) then a else b) x.2) := by
  let step : PolyProgram (encodePair ea ea) ea (fun x => if p x then x.2 else x.1) :=
    (ite P (fst ea ea) (snd ea ea)).congr _ (fun _ => rfl)
  exact step.listFold a0 X (fun as b pre suf he => by
    rcases ListAlgorithms.foldChoice p pre b with h|h
    · rw [h]
      simp only [eval_X,encodePair_length]; omega
    · have hp : (encodeList ea pre).length ≤ (encodeList ea as).length := by
        rw [he,EncodedList.append,List.length_append]; omega
      have hh := (EncodedList.member_length ea pre _ h).trans hp
      simp only [eval_X,encodePair_length]; omega)
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Optimization.LPListFacts -/
section
namespace OAI


                                   
section
namespace MetricKMedian.LPBinary
open Finset
abbrev Row := List ℚ
abbrev Rows := List Row
abbrev er := Binary.encodeList Binary.Ratio.encode
abbrev ers := Binary.encodeList er

 theorem foldl_max_le {α : Type} [LinearOrder α] (xs : List α) (a b : α)
    (ha : a ≤ b) (hx : ∀ x∈xs, x≤b) : xs.foldl max a ≤ b := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
      exact ih (max a x) (max_le ha (hx x List.mem_cons_self)) (fun y hy => hx y (List.mem_cons_of_mem _ hy))

 theorem le_foldl_max {α : Type} [LinearOrder α] (xs : List α) (a : α) : a ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => exact le_rfl
  | cons x xs ih => exact (le_max_left a x).trans (ih (max a x))

 theorem member_le_foldl_max {α : Type} [LinearOrder α] (xs : List α) (a b : α) (hb : b∈xs) : b ≤ xs.foldl max a := by
  induction xs generalizing a with
  | nil => cases hb
  | cons x xs ih =>
      rcases List.mem_cons.mp hb with rfl|hb
      · exact (le_max_right a b).trans (le_foldl_max xs (max a b))
      · exact ih (max a x) hb

 theorem foldl_max_eq {α : Type} [LinearOrder α] (xs : List α) (a b : α)
    (ha : a ≤ b) (hb : b∈xs) (hx : ∀ x∈xs, x≤b) : xs.foldl max a=b :=
  le_antisymm (foldl_max_le xs a b ha hx) (member_le_foldl_max xs a b hb)

 theorem sum_filter_ofFn (n : ℕ) (f : Fin n → ℚ) (p : ℚ → Bool) :
    ((List.ofFn f).filter p).sum=∑ i∈univ.filter (fun i => p (f i)), f i := by
  rw [Finset.sum_filter]
  have he : ((List.ofFn f).filter p).sum=((List.ofFn f).map (fun a => if p a then a else 0)).sum := by
    generalize List.ofFn f=xs
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih]
  rw [he,List.map_ofFn,List.sum_ofFn]
  rfl

 theorem length_filter_ofFn (n : ℕ) (f : Fin n → ℚ) (p : ℚ → Bool) :
    ((List.ofFn f).filter p).length=(univ.filter (fun i => p (f i))).card := by
  have he : ((List.ofFn f).filter p).length=((List.ofFn f).map (fun a => if p a then (1:ℕ) else 0)).sum := by
    generalize List.ofFn f=xs
    induction xs with
    | nil => rfl
    | cons a xs ih => cases h : p a <;> simp [h,ih,Nat.add_comm]
  rw [he,List.map_ofFn,List.sum_ofFn]
  simp

namespace Program
open Binary Binary.PolyProgram
noncomputable def ratMax : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => max x.1 x.2) :=
  (ite ratLE (fst Ratio.encode Ratio.encode) (snd Ratio.encode Ratio.encode)).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [h]
    · simp [h,max_eq_left (le_of_not_ge h)])
noncomputable def ratMin : PolyProgram (encodePair Ratio.encode Ratio.encode) Ratio.encode (fun x : ℚ × ℚ => min x.1 x.2) :=
  (ite ratLE (snd Ratio.encode Ratio.encode) (fst Ratio.encode Ratio.encode)).congr _ (fun x => by
    by_cases h : x.1≤x.2
    · simp [h]
    · simp [h,min_eq_right (le_of_not_ge h)])
noncomputable def maxFold : PolyProgram (encodePair er Ratio.encode) Ratio.encode (fun x : Row × ℚ => x.1.foldl max x.2) :=
  (listChoose ratLT 0).congr _ (fun x => by
    congr 1
    funext a b
    by_cases h : a<b
    · simp [h,max_eq_right h.le]
    · simp [h,max_eq_left (le_of_not_gt h)])
end Program
end MetricKMedian.LPBinary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryAutomatic -/
section
namespace OAI


                                       
section
namespace MetricKMedian.Binary.Automatic
open PolyProgram Function
class Coding (α : Type) where
  encode : α → List Bool
abbrev enc {α : Type} [Coding α] : α → List Bool := Coding.encode
instance : Coding ℕ := ⟨Nat.bits⟩
instance : Coding ℤ := ⟨Signed.encode⟩
instance : Coding ℚ := ⟨Ratio.encode⟩
instance : Coding Bool := ⟨encodeBool⟩
instance : Coding Unit := ⟨fun _ => []⟩
instance {α β : Type} [Coding α] [Coding β] : Coding (α × β) := ⟨encodePair enc enc⟩
instance {α : Type} [Coding α] : Coding (List α) := ⟨encodeList enc⟩

@[fun_prop] def Poly {α β : Type} [Coding α] [Coding β] (f : α → β) : Prop :=
  Nonempty (PolyProgram enc enc f)

namespace Poly
variable {α β γ : Type} [Coding α] [Coding β] [Coding γ]
noncomputable def program {f : α → β} (h : Poly f) : PolyProgram enc enc f := Classical.choice h

theorem of_program {f : α → β} (p : PolyProgram enc enc f) : Poly f := ⟨p⟩

@[fun_prop] theorem identity : Poly (id : α → α) := ⟨PolyProgram.identity enc⟩
@[fun_prop] theorem const (b : β) : Poly (fun _ : α => b) := ⟨PolyProgram.constant enc enc b⟩
@[fun_prop] theorem comp {f : β → γ} {g : α → β} (hf : Poly f) (hg : Poly g) : Poly (fun a => f (g a)) :=
  ⟨hg.program.comp hf.program⟩
@[fun_prop] theorem pair {f : α → β} {g : α → γ} (hf : Poly f) (hg : Poly g) : Poly (fun a => (f a,g a)) :=
  ⟨hf.program.fanout hg.program⟩
@[fun_prop] theorem fst : Poly (Prod.fst : α × β → α) := ⟨PolyProgram.fst enc enc⟩
@[fun_prop] theorem snd : Poly (Prod.snd : α × β → β) := ⟨PolyProgram.snd enc enc⟩
@[fun_prop] theorem ite {p : α → Bool} {f g : α → β} (hp : Poly p) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x then f x else g x) := ⟨(PolyProgram.ite hp.program hg.program hf.program).congr _ (fun _ => rfl)⟩

@[fun_prop] theorem list_map [Inhabited β] [Inhabited γ] {f : α → β → γ} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).map (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listMapWith default default)⟩

@[fun_prop] theorem rat_add : Poly (fun x : ℚ × ℚ => x.1+x.2) := ⟨ratAdd⟩
@[fun_prop] theorem rat_sub : Poly (fun x : ℚ × ℚ => x.1-x.2) := ⟨ratSub⟩
@[fun_prop] theorem rat_mul : Poly (fun x : ℚ × ℚ => x.1*x.2) := ⟨ratMul⟩
@[fun_prop] theorem rat_div : Poly (fun x : ℚ × ℚ => x.1/x.2) := ⟨ratDiv⟩
@[fun_prop] theorem rat_lt : Poly (fun x : ℚ × ℚ => decide (x.1<x.2)) := ⟨ratLT⟩
@[fun_prop] theorem rat_le : Poly (fun x : ℚ × ℚ => decide (x.1≤x.2)) := ⟨ratLE⟩
@[fun_prop] theorem rat_eq : Poly (fun x : ℚ × ℚ => decide (x.1=x.2)) := ⟨ratEQ⟩
@[fun_prop] theorem rat_min : Poly (fun x : ℚ × ℚ => min x.1 x.2) := ⟨LPBinary.Program.ratMin⟩
@[fun_prop] theorem rat_max : Poly (fun x : ℚ × ℚ => max x.1 x.2) := ⟨LPBinary.Program.ratMax⟩
@[fun_prop] theorem nat_add : Poly (fun x : ℕ × ℕ => x.1+x.2) := ⟨natAdd⟩
@[fun_prop] theorem nat_sub : Poly (fun x : ℕ × ℕ => x.1-x.2) := ⟨natSub⟩
@[fun_prop] theorem nat_mul : Poly (fun x : ℕ × ℕ => x.1*x.2) := ⟨natMul⟩
@[fun_prop] theorem nat_lt : Poly (fun x : ℕ × ℕ => decide (x.1<x.2)) := ⟨natLT⟩
@[fun_prop] theorem nat_le : Poly (fun x : ℕ × ℕ => decide (x.1≤x.2)) := ⟨natLE⟩
@[fun_prop] theorem nat_eq : Poly (fun x : ℕ × ℕ => decide (x.1=x.2)) := ⟨natEQ⟩
@[fun_prop] theorem bool_and : Poly (fun x : Bool × Bool => x.1 && x.2) := ⟨boolAnd⟩
@[fun_prop] theorem bool_or : Poly (fun x : Bool × Bool => x.1 || x.2) := ⟨boolOr⟩
@[fun_prop] theorem rat_neg : Poly (fun x : ℚ => -x) := ⟨ratNeg⟩
@[fun_prop] theorem bool_not : Poly (fun x : Bool => !x) := ⟨boolNot⟩
@[fun_prop] theorem rat_ofNat : Poly (fun x : ℕ => (x:ℚ)) := ⟨ratOfNat⟩
@[fun_prop] theorem rat_ofInt : Poly (fun x : ℤ => (x:ℚ)) := ⟨ratOfInt⟩

@[fun_prop] theorem list_length [Inhabited α] : Poly (List.length : List α → ℕ) := ⟨listLength enc default⟩
@[fun_prop] theorem list_indices [Inhabited α] : Poly (fun xs : List α => List.range xs.length) := ⟨listIndices enc default⟩
@[fun_prop] theorem list_getD (a0 : α) : Poly (fun x : List α × ℕ => x.1[x.2]?.getD a0) := ⟨listGetD enc a0⟩
@[fun_prop] theorem list_head (a0 : α) : Poly (fun xs : List α => xs.head?.getD a0) := ⟨listHead enc a0⟩
@[fun_prop] theorem list_tail [Inhabited α] : Poly (List.tail : List α → List α) := ⟨listTail enc default⟩
@[fun_prop] theorem list_empty : Poly (List.isEmpty : List α → Bool) := ⟨listIsEmpty enc⟩
@[fun_prop] theorem list_append [Inhabited α] : Poly (fun x : List α × List α => x.1++x.2) := ⟨listAppend enc default⟩
@[fun_prop] theorem list_cons : Poly (fun x : α × List α => x.1::x.2) := ⟨listCons enc⟩
@[fun_prop] theorem list_zip [Inhabited α] [Inhabited β] : Poly (fun x : List α × List β => x.1.zip x.2) := ⟨listZip enc enc default default⟩
@[fun_prop] theorem list_filter [Inhabited α] [Inhabited β] {f : α → β → Bool} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).filter (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listFilterWith default default)⟩
@[fun_prop] theorem list_findIdx [Inhabited β] {f : α → β → Bool} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).findIdx (f x)) := by
  let tests := ((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listMapWith default false)
  exact ⟨(tests.comp (listFindIdx (PolyProgram.identity encodeBool) false)).congr _ (fun _ => by
    simp only [Function.comp_def,List.findIdx_map,id_eq])⟩

@[fun_prop] theorem list_getD_comp (a0 : β) {xs : α → List β} {i : α → ℕ}
    (hx : Poly xs) (hi : Poly i) : Poly (fun x => (xs x)[i x]?.getD a0) :=
  comp (list_getD a0) (pair hx hi)
@[fun_prop] theorem list_head_comp (a0 : β) {xs : α → List β}
    (hx : Poly xs) : Poly (fun x => (xs x).head?.getD a0) := comp (list_head a0) hx

@[fun_prop] theorem rat_lt_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x<g x)) := comp rat_lt (pair hf hg)
@[fun_prop] theorem rat_le_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x≤g x)) := comp rat_le (pair hf hg)
@[fun_prop] theorem rat_eq_comp {f g : α → ℚ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x=g x)) := comp rat_eq (pair hf hg)
@[fun_prop] theorem nat_lt_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x<g x)) := comp nat_lt (pair hf hg)
@[fun_prop] theorem nat_le_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x≤g x)) := comp nat_le (pair hf hg)
@[fun_prop] theorem nat_eq_comp {f g : α → ℕ} (hf : Poly f) (hg : Poly g) : Poly (fun x => decide (f x=g x)) := comp nat_eq (pair hf hg)
@[fun_prop] theorem ite_prop {p : α → Prop} [DecidablePred p] {f g : α → β}
    (hp : Poly (fun x => decide (p x))) (hf : Poly f) (hg : Poly g) :
    Poly (fun x => if p x then f x else g x) := by
  exact ⟨(PolyProgram.ite hp.program hg.program hf.program).congr _ (fun _ => by simp only [decide_eq_true_eq])⟩

@[fun_prop] theorem list_flatMap [Inhabited β] [Inhabited γ] {f : α → β → List γ} {as : α → List β}
    (hf : Poly (fun x : α × β => f x.1 x.2)) (ha : Poly as) :
    Poly (fun x => (as x).flatMap (f x)) :=
  ⟨((PolyProgram.identity enc).fanout ha.program).comp (hf.program.listFlatMapWith default default)⟩

end Poly
end MetricKMedian.Binary.Automatic
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryRationalFold -/
section
namespace OAI


                                          
section
namespace MetricKMedian.Binary
open Function Polynomial
namespace HasHeight
 theorem foldAdd (as : List ℚ) (b : ℚ) (L : ℕ) (hb : HasHeight b L) :
    HasHeight (as.foldl (·+·) b) (L+(encodeList Ratio.encode as).length) := by
  induction as generalizing b L with
  | nil => simpa only [List.foldl_nil,EncodedList.nil,List.length_nil,add_zero] using hb
  | cons a as ih =>
      have hh := ih (b+a) (L+(Ratio.encode a).length+1) (hb.add (Ratio.height_length a))
      simp only [List.foldl_cons,EncodedList.cons_length]
      exact hh.mono (by omega)
 theorem foldMul (as : List ℚ) (b : ℚ) (L : ℕ) (hb : HasHeight b L) :
    HasHeight (as.foldl (·*·) b) (L+(encodeList Ratio.encode as).length) := by
  induction as generalizing b L with
  | nil => simpa only [List.foldl_nil,EncodedList.nil,List.length_nil,add_zero] using hb
  | cons a as ih =>
      have hh := ih (b*a) (L+(Ratio.encode a).length) (hb.mul (Ratio.height_length a))
      simp only [List.foldl_cons,EncodedList.cons_length]
      exact hh.mono (by omega)
end HasHeight
namespace ListAlgorithms
 theorem foldAdd (as : List ℚ) (b : ℚ) : as.foldl (·+·) b=b+as.sum := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.sum_cons,add_assoc]
 theorem foldMul (as : List ℚ) (b : ℚ) : as.foldl (·*·) b=b*as.prod := by
  induction as generalizing b with
  | nil => simp
  | cons a as ih => simp only [List.foldl_cons,ih,List.prod_cons,mul_assoc]
end ListAlgorithms
namespace PolyProgram
noncomputable def ratFoldAdd : PolyProgram (encodePair (encodeList Ratio.encode) Ratio.encode)
    Ratio.encode (fun x : List ℚ × ℚ => x.1.foldl (·+·) x.2) :=
  ratAdd.listFold 0 (3*X+10) (fun as b pre suf he => by
    have hh := Ratio.length_height (HasHeight.foldAdd pre b (Ratio.encode b).length (Ratio.height_length b))
    have hp : (encodeList Ratio.encode pre).length ≤ (encodeList Ratio.encode as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    simp only [encodePair_length,eval_add,eval_mul,eval_ofNat,eval_X]
    omega)
noncomputable def ratFoldMul : PolyProgram (encodePair (encodeList Ratio.encode) Ratio.encode)
    Ratio.encode (fun x : List ℚ × ℚ => x.1.foldl (·*·) x.2) :=
  ratMul.listFold 0 (3*X+10) (fun as b pre suf he => by
    have hh := Ratio.length_height (HasHeight.foldMul pre b (Ratio.encode b).length (Ratio.height_length b))
    have hp : (encodeList Ratio.encode pre).length ≤ (encodeList Ratio.encode as).length := by
      rw [he,EncodedList.append,List.length_append]; omega
    simp only [encodePair_length,eval_add,eval_mul,eval_ofNat,eval_X]
    omega)
noncomputable def ratSum : PolyProgram (encodeList Ratio.encode) Ratio.encode List.sum := by
  refine (((identity (encodeList Ratio.encode)).fanout (constant (encodeList Ratio.encode) Ratio.encode 0)).comp ratFoldAdd).congr _ ?_
  intro as
  simp only [Function.comp_apply,id_eq]
  simpa only [zero_add] using ListAlgorithms.foldAdd as 0
noncomputable def ratProd : PolyProgram (encodeList Ratio.encode) Ratio.encode List.prod := by
  refine (((identity (encodeList Ratio.encode)).fanout (constant (encodeList Ratio.encode) Ratio.encode 1)).comp ratFoldMul).congr _ ?_
  intro as
  simp only [Function.comp_apply,id_eq]
  simpa only [one_mul] using ListAlgorithms.foldMul as 1
end PolyProgram
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.BinaryBooleanLists -/
section
namespace OAI


                                          
section
namespace MetricKMedian.Binary
namespace BooleanLists
def pack : Transducer where
  Q := Unit
  initial := ()
  next := fun _ b => ((),[true,b,false])
  finish := fun _ => []
 theorem pack_run (xs : List Bool) : pack.run () xs=encodeList encodeBool xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [Transducer.run,pack,encodeList,encodeBool,quote,List.append_assoc,List.nil_append] using congrArg (fun ys => [true,b,false]++ys) ih
inductive Phase | start | value | stop deriving DecidableEq
instance : Fintype Phase := ⟨{.start,.value,.stop},by intro p; cases p <;> simp⟩
def unpack : Transducer where
  Q := Phase
  initial := .start
  next := fun q b => match q with
    | .start => (.value,[])
    | .value => (.stop,[b])
    | .stop => (.start,[])
  finish := fun _ => []
 theorem unpack_run (xs : List Bool) : unpack.run .start (encodeList encodeBool xs)=xs := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simpa only [encodeList,encodeBool,quote,List.cons_append,List.nil_append,Transducer.run,unpack,List.append_assoc,List.singleton_append] using congrArg (List.cons b) ih
noncomputable def packProgram : PolyProgram id (encodeList encodeBool) (id : List Bool → List Bool) :=
  pack.program.recode id (fun _ => rfl) (fun xs => pack_run xs)
noncomputable def unpackProgram : PolyProgram (encodeList encodeBool) id (id : List Bool → List Bool) :=
  unpack.program.recode (encodeList encodeBool) (fun _ => rfl) (fun xs => unpack_run xs)
noncomputable def valueProgram : PolyProgram (encodeList encodeBool) Nat.bits Word.value := unpackProgram.comp PolyProgram.toBits
 theorem length (xs : List Bool) : (encodeList encodeBool xs).length=3*xs.length := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [EncodedList.cons_length,encodeBool,List.length_cons,List.length_nil,ih]; omega
end BooleanLists
end MetricKMedian.Binary
end

end OAI
end

/- OAI.Combinatorics.KMedian.Model -/
section
namespace OAI




section
section
namespace MetricKMedian

structure Instance where
  n : ℕ
  distance : Fin n → Fin n → ℚ
  clients : Finset (Fin n)
  facilities : Finset (Fin n)
  k : ℕ
  distance_nonneg : ∀ i j, 0 ≤ distance i j
  distance_eq_zero : ∀ i j, distance i j = 0 ↔ i = j
  distance_symm : ∀ i j, distance i j = distance j i
  distance_triangle : ∀ i j h, distance i h ≤ distance i j + distance j h
  k_pos : 1 ≤ k
  k_le : k ≤ facilities.card

def encodeNat (n : ℕ) : List Bool :=
  List.replicate n.bits.length true ++ [false] ++ n.bits

def encodeRat (q : ℚ) : List Bool :=
  [decide (q.num < 0)] ++ encodeNat q.num.natAbs ++ encodeNat q.den

def encodeInstance (I : Instance) : List Bool :=
  encodeNat I.n ++ encodeNat I.k ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.clients)) ++
    List.ofFn (fun i : Fin I.n => decide (i ∈ I.facilities)) ++
    (List.ofFn (fun i : Fin I.n =>
      (List.ofFn (fun j : Fin I.n => encodeRat (I.distance i j))).flatten)).flatten

noncomputable def nearest (I : Instance) (j : Fin I.n) (S : Finset (Fin I.n)) : ℝ :=
  if h : S.Nonempty then
    (S.image (fun i => (I.distance j i : ℝ))).min' (h.image _)
  else 0

noncomputable def cost (I : Instance) (S : Finset (Fin I.n)) : ℝ :=
  ∑ j ∈ I.clients, nearest I j S

def feasibleSets (I : Instance) : Finset (Finset (Fin I.n)) :=
  I.facilities.powerset.filter (fun S => S.Nonempty ∧ S.card ≤ I.k)

noncomputable def optimum (I : Instance) : ℝ :=
  if h : (feasibleSets I).Nonempty then
    ((feasibleSets I).image (cost I)).min' (h.image _)
  else 0

def Correct (epsilon : ℝ) (I : Instance) (output : List Bool) : Prop :=
  ∃ S : Finset (Fin I.n), S ⊆ I.facilities ∧ S.Nonempty ∧ S.card ≤ I.k ∧
    output = List.ofFn (fun i : Fin I.n => decide (i ∈ S)) ∧
    cost I S ≤ (1 + 2 / Real.exp 1 + epsilon) * optimum I


end MetricKMedian
end
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.NumericParserProgram -/
section
namespace OAI


                                            
section
namespace MetricKMedian.InputParser
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly
@[fun_prop] theorem take_poly {α : Type} [Coding α] [Inhabited α] : Poly (fun x : List α × ℕ => x.1.take x.2) := ⟨listTake enc default⟩
@[fun_prop] theorem drop_poly {α : Type} [Coding α] [Inhabited α] : Poly (fun x : List α × ℕ => x.1.drop x.2) := ⟨listDrop enc default⟩
@[fun_prop] theorem value_poly : Poly Word.value := ⟨BooleanLists.valueProgram⟩
@[fun_prop] theorem signed_poly : Poly (fun x : Bool × ℕ => Signed.value x.1 x.2) := ⟨intFromParts⟩
@[fun_prop] theorem mkRat_poly : Poly (fun x : ℤ × ℕ => mkRat x.1 x.2) := ⟨mkRational⟩
def width (xs : List Bool) : ℕ := xs.findIdx Bool.not
@[fun_prop] theorem width_poly : Poly width := by unfold width; apply list_findIdx <;> fun_prop
def natRead (xs : List Bool) : ℕ × List Bool :=
  (Word.value ((xs.drop (width xs+1)).take (width xs)),xs.drop (width xs+1+width xs))
@[fun_prop] theorem natRead_poly : Poly natRead := by
  have hd : Poly (fun xs : List Bool => xs.drop (width xs+1)) :=
    Poly.comp (f:=fun x : List Bool × ℕ => x.1.drop x.2) drop_poly (g:=fun xs : List Bool => (xs,width xs+1)) (by fun_prop)
  have ht : Poly (fun xs : List Bool => (xs.drop (width xs+1)).take (width xs)) :=
    Poly.comp (f:=fun x : List Bool × ℕ => x.1.take x.2) take_poly (pair hd width_poly)
  exact pair (Poly.comp value_poly ht) (Poly.comp (f:=fun x : List Bool × ℕ => x.1.drop x.2) drop_poly (g:=fun xs : List Bool => (xs,width xs+1+width xs)) (by fun_prop))
 theorem prefix_width (n : ℕ) (xs : List Bool) : width (List.replicate n true++false::xs)=n := by
  induction n with
  | zero => simp [width,List.findIdx_cons]
  | succ n ih => simp only [List.replicate_succ,List.cons_append,width,List.findIdx_cons,Bool.not_true,Bool.false_eq_true,↓reduceIte]; exact congrArg Nat.succ ih
 theorem natRead_append (n : ℕ) (xs : List Bool) : natRead (encodeNat n++xs)=(n,xs) := by
  unfold natRead
  have hw : width (encodeNat n++xs)=n.bits.length := by
    simpa only [encodeNat,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using prefix_width n.bits.length (n.bits++xs)
  rw [hw]
  have hd : (encodeNat n++xs).drop (n.bits.length+1)=n.bits++xs := by
    simp [encodeNat,List.drop_append,List.append_assoc]
  rw [hd,show (encodeNat n++xs).drop (n.bits.length+1+n.bits.length)=xs from by
    rw [← List.drop_drop,hd,List.drop_left]]
  simp only [List.take_left,Word.value_bits]
 theorem natRead_rest_length (xs : List Bool) : (natRead xs).2.length≤xs.length := by
  simp only [natRead,List.length_drop]; omega
def ratRead (xs : List Bool) : ℚ × List Bool :=
  let a := natRead xs.tail
  let b := natRead a.2
  (mkRat (Signed.value (xs.head?.getD false) a.1) b.1,b.2)
@[fun_prop] theorem ratRead_poly : Poly ratRead := by unfold ratRead; fun_prop
 theorem ratRead_append (q : ℚ) (xs : List Bool) : ratRead (encodeRat q++xs)=(q,xs) := by
  simp only [ratRead,encodeRat,List.append_assoc,List.cons_append,List.tail_cons,List.head?_cons,Option.getD_some,List.nil_append,natRead_append]
  rw [show Signed.value (decide (q.num<0)) q.num.natAbs=q.num from Signed.value_parts q.num]
  rw [Rat.mkRat_eq_div,q.num_div_den]
 theorem ratRead_rest_length (xs : List Bool) : (ratRead xs).2.length≤xs.length :=
  (natRead_rest_length _).trans ((natRead_rest_length _).trans (by simp only [List.length_tail]; omega))
end MetricKMedian.InputParser
end

end OAI
end

/- OAI.Combinatorics.KMedian.Binary.SequentialParserProgram -/
section
namespace OAI


                                               
section
namespace MetricKMedian.InputParser
open Binary Binary.PolyProgram Binary.Automatic Binary.Automatic.Poly Polynomial
section Generic
variable {α : Type} [Coding α] [Inhabited α] (read : List Bool → α × List Bool)
abbrev State := List Bool × List α
def parseStep (x : State (α:=α) × Unit) : State (α:=α) :=
  let s := read x.1.1
  (s.2,s.1::x.1.2)
 omit [Inhabited α] in
 theorem parseStep_poly (h : Poly read) : Poly (parseStep read) := by
  unfold parseStep
  have hh : Poly (fun x : State (α:=α) × Unit => read x.1.1) := Poly.comp h (by fun_prop)
  have ha : Poly (fun x : State (α:=α) × Unit => (read x.1.1).1 :: x.1.2) :=
    Poly.comp (f:=fun y : α × List α => y.1::y.2) list_cons (g:=fun x : State (α:=α) × Unit => ((read x.1.1).1,x.1.2)) (by fun_prop)
  exact pair (by fun_prop) ha
variable (P : PolyProgram enc enc read) (hrest : ∀ xs, (read xs).2.length≤xs.length)
noncomputable def parseBound : Polynomial ℕ := X+X*(2*P.sizeBound+1)
 omit [Inhabited α] in
 include hrest in
 theorem parseFold_size (as : List Unit) (b : State (α:=α)) :
    let out := as.foldl (fun b a => parseStep read (b,a)) b
    out.1.length≤b.1.length ∧
    (enc out.2).length≤(enc b.2).length+as.length*(2*P.sizeBound.eval (enc b.1).length+1) := by
  induction as generalizing b with
  | nil => simp only [List.foldl_nil,List.length_nil,zero_mul,add_zero]; exact ⟨le_rfl,le_rfl⟩
  | cons a as ih =>
    have hh := ih (parseStep read (b,a))
    have hr := hrest b.1
    have hs := P.length_bound b.1
    have he : (enc ((read b.1).1)).length ≤ P.sizeBound.eval (enc b.1).length := by
      change (encodePair enc enc (read b.1)).length≤_ at hs
      rw [encodePair_length] at hs
      omega
    have hp : P.sizeBound.eval (enc (read b.1).2).length≤P.sizeBound.eval (enc b.1).length := by
      apply polynomial_eval_mono
      change (encodeList encodeBool (read b.1).2).length≤(encodeList encodeBool b.1).length
      rw [BooleanLists.length,BooleanLists.length]
      omega
    dsimp only [parseStep] at hh
    simp only [List.foldl_cons,List.length_cons]
    refine ⟨hh.1.trans hr,?_⟩
    have hc : (enc ((read b.1).1::b.2)).length=2*(enc (read b.1).1).length+1+(enc b.2).length := EncodedList.cons_length _ _ _
    rw [hc] at hh
    exact hh.2.trans (by nlinarith)
noncomputable def foldProgram : PolyProgram enc enc
    (fun x : List Unit × State (α:=α) => x.1.foldl (fun b a => parseStep read (b,a)) x.2) :=
  (parseStep_poly read ⟨P⟩).program.listFold () (parseBound read P) (by
    intro as b pre suf he
    have hh := parseFold_size read P hrest pre b
    let L := (enc (as,b)).length
    have hb : (enc b).length≤L := by
      dsimp only [L]
      change (enc b).length≤(encodePair enc enc (as,b)).length
      rw [encodePair_length]; dsimp only; omega
    have hp : pre.length≤L := by
      have ha := EncodedList.length_le (enc : Unit → List Bool) as
      have hl : pre.length≤as.length := by rw [he,List.length_append]; omega
      change as.length≤(enc as).length at ha
      dsimp only [L]
      change pre.length≤(encodePair enc enc (as,b)).length
      rw [encodePair_length]; dsimp only; omega
    have hx : (enc b.1).length≤L := by
      change (encodePair enc enc b).length≤L at hb
      rw [encodePair_length] at hb; omega
    have hq := polynomial_eval_mono P.sizeBound hx
    have hr : (enc (pre.foldl (fun b a => parseStep read (b,a)) b).1).length≤(enc b.1).length := by
      change (encodeList encodeBool _).length≤(encodeList encodeBool _).length
      rw [BooleanLists.length,BooleanLists.length]; omega
    change (encodePair enc enc _).length≤_
    rw [encodePair_length]
    change (encodePair enc enc b).length≤L at hb
    rw [encodePair_length] at hb
    simp only [parseBound,eval_add,eval_X,eval_mul,eval_ofNat,eval_one]
    change _≤L+L*(2*P.sizeBound.eval L+1)
    have hm := Nat.mul_le_mul hp (show 2*P.sizeBound.eval (enc b.1).length+1≤2*P.sizeBound.eval L+1 by omega)
    have hh2 := hh.2
    omega)
def parse (x : List Unit × List Bool) : List α × List Bool :=
  let s := x.1.foldl (fun b a => parseStep read (b,a)) (x.2,[])
  (s.2.reverse,s.1)
noncomputable def parseProgram : PolyProgram enc enc (parse read) := by
  have h : Poly (fun x : List Unit × List Bool => (x.1,(x.2,([] : List α)))) := by fun_prop
  have hv : Poly (List.reverse : List α → List α) := ⟨listReverse enc default⟩
  have g : Poly (fun x : State (α:=α) => (x.2.reverse,x.1)) := pair (Poly.comp hv snd) fst
  exact h.program.comp (foldProgram read P hrest) |>.comp g.program
 omit [Coding α] [Inhabited α] in
 theorem parse_fold_encoded (put : α → List Bool) (hr : ∀ a xs, read (put a++xs)=(a,xs))
    (as : List α) (xs : List Bool) (acc : List α) :
    (List.replicate as.length ()).foldl (fun b a => parseStep read (b,a)) ((as.map put).flatten++xs,acc)=
      (xs,as.reverse++acc) := by
  induction as generalizing acc with
  | nil => simp
  | cons a as ih =>
    simp only [List.length_cons,List.replicate_succ,List.map_cons,List.flatten_cons,List.append_assoc,
      List.foldl_cons,parseStep,hr]
    change (List.replicate as.length ()).foldl (fun b a => parseStep read (b,a)) ((as.map put).flatten++xs,a::acc)=_
    rw [ih]
    simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
 omit [Coding α] [Inhabited α] in
 theorem parse_encoded (put : α → List Bool) (hr : ∀ a xs, read (put a++xs)=(a,xs))
    (as : List α) (xs : List Bool) :
    parse read (List.replicate as.length (),(as.map put).flatten++xs)=(as,xs) := by
  unfold parse
  rw [parse_fold_encoded read put hr]
  simp
end Generic
end MetricKMedian.InputParser
end

end OAI
end

/- Hybrid -/
section
namespace DualSepClusterLP.Dense
variable {ι : Type} (A : ι → ι → ℚ)

theorem greedy_sublist (est : ι → ℚ) (xs : List ι) (b : ι → ℚ) :
    (greedy A est xs b).Sublist xs := by
  induction xs generalizing b with
  | nil => simp [greedy]
  | cons i xs ih =>
    rw [greedy]; split
    · exact (ih _).cons₂ _
    · exact (ih _).cons _

end DualSepClusterLP.Dense
end

/- RawGreedy -/
section
namespace DualSepClusterLP.ScanDense
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly
variable {D : Type} [Coding D]
abbrev Ctx (D : Type) := D × (List ℕ × (ℕ × ℕ × ℕ × List Bool))
abbrev Scan (D : Type) := Ctx D × List ℕ

@[fun_prop] theorem idx_poly {α : Type} [Coding α] {xs : α → List ℕ} {f : α → ℕ}
    (hxs : Poly xs) (hf : Poly f) : Poly (fun a => (xs a).idxOf (f a)) := by
  have ht : Poly (fun a : α => (xs a).findIdx (fun i => decide (i = f a))) :=
    list_findIdx (by fun_prop) hxs
  exact ⟨ht.program.congr _ (fun a => by
    unfold List.idxOf; congr 1)⟩

@[fun_prop] private theorem mod_comp {α : Type} [Coding α] {f g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun a => f a % g a) := comp (f:=fun x : ℕ × ℕ => x.1 % x.2) ⟨PolyProgram.natMod⟩ (pair hf hg)

private theorem radd {α : Type} [Coding α] {f g : α → ℚ} (hf : Poly f) (hg : Poly g) :
    Poly (fun a => f a + g a) := comp rat_add (pair hf hg)
private theorem rmul {α : Type} [Coding α] {f g : α → ℚ} (hf : Poly f) (hg : Poly g) :
    Poly (fun a => f a * g a) := comp rat_mul (pair hf hg)
private theorem band {α : Type} [Coding α] {f g : α → Bool} (hf : Poly f) (hg : Poly g) :
    Poly (fun a => f a && g a) := comp bool_and (pair hf hg)
private theorem append1 {α : Type} [Coding α] {f : α → List ℕ} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun a => f a ++ [g a]) := comp list_append (pair hf (comp list_cons (pair hg (by fun_prop : Poly (fun _ : α => ([] : List ℕ))))))

def pos (cfg : Ctx D) (l : ℕ) := (cfg.2.2.2.1*l+cfg.2.2.2.2.1)%cfg.2.2.1

def estimate (A : D → ℕ → ℕ → ℚ) (c : Ctx D) (i : ℕ) : ℚ :=
  let u := c.2.1
  let bits := c.2.2.2.2.2
  (c.2.2.1:ℚ)/bits.length *
    ((List.range bits.length).map (fun l =>
      if (decide (u.idxOf i < pos c l) && decide (pos c l < u.length)) && bits[l]?.getD false
      then A c.1 i (u[pos c l]?.getD 0) else 0)).sum

variable (A : D → ℕ → ℕ → ℚ) (b : D → ℕ → ℚ)

theorem estimate_poly (ha : Poly (fun p : D × ℕ × ℕ => A p.1 p.2.1 p.2.2)) :
    Poly (fun v : Ctx D × ℕ => estimate A v.1 v.2) := by
  have ha' {α : Type} [Coding α] {d : α→D} {i j : α→ℕ}
      (hd : Poly d) (hi : Poly i) (hj : Poly j) : Poly (fun z => A (d z) (i z) (j z)) :=
    comp ha (pair hd (pair hi hj))
  unfold estimate pos
  apply rmul
  · fun_prop
  · apply Poly.comp (f:=List.sum) (show Poly (List.sum : List ℚ → ℚ) from ⟨PolyProgram.ratSum⟩)
    apply list_map
    · apply Poly.ite
      · apply band
        · apply band <;> fun_prop
        · fun_prop
      · apply ha' <;> fun_prop
      · fun_prop
    · exact comp (f:=fun xs : List Bool => List.range xs.length) list_indices (by fun_prop)

def push (z : Scan D × ℕ) : Scan D :=
  let c := z.1.1
  let sel := z.1.2
  let i := z.2
  let cost := b c.1 i + (sel.map (fun j => A c.1 j i)).sum + estimate A c i
  (c, if cost ≤ 0 then sel ++ [i] else sel)

theorem push_poly (ha : Poly (fun p : D × ℕ × ℕ => A p.1 p.2.1 p.2.2))
    (hb : Poly (fun p : D × ℕ => b p.1 p.2)) : Poly (push A b) := by
  have ha' {α : Type} [Coding α] {d : α→D} {i j : α→ℕ}
      (hd : Poly d) (hi : Poly i) (hj : Poly j) : Poly (fun z => A (d z) (i z) (j z)) :=
    comp ha (pair hd (pair hi hj))
  unfold push
  apply pair (by fun_prop)
  apply ite_prop
  · apply rat_le_comp _ (by fun_prop)
    apply radd
    · apply radd
      · exact comp hb (g:=fun z : Scan D × ℕ => (z.1.1.1,z.2)) (by fun_prop)
      · apply Poly.comp (f:=List.sum) (show Poly (List.sum : List ℚ → ℚ) from ⟨PolyProgram.ratSum⟩)
        apply list_map
        · apply ha' <;> fun_prop
        · fun_prop
    · exact comp (estimate_poly A ha) (g:=fun z : Scan D × ℕ => (z.1.1,z.2)) (by fun_prop)
  · apply append1 <;> fun_prop
  · fun_prop

def run (c : Ctx D) : List ℕ := (c.2.1.foldl (fun s i => push A b (s,i)) (c,[])).2

theorem run_poly (ha : Poly (fun p : D × ℕ × ℕ => A p.1 p.2.1 p.2.2))
    (hb : Poly (fun p : D × ℕ => b p.1 p.2)) : Poly (run A b) := by
  let P := (push_poly A b ha hb).program
  let F := P.listFoldLinear 0 1 (by
    intro s a
    change (encodePair _ _ (s.1,if _ then s.2++[a] else s.2)).length ≤
      (encodePair _ _ s).length+1*(2*(enc a).length+1)
    simp only [encodePair_length,one_mul]
    split
    · change 2*(enc s.1).length+1+(encodeList Nat.bits (s.2++[a])).length ≤ 2*(enc s.1).length+1+(encodeList Nat.bits s.2).length+(2*a.bits.length+1)
      rw [EncodedList.append,List.length_append,EncodedList.cons_length,EncodedList.nil]
      simp only [List.length_nil,add_zero]; omega
    · omega)
  have hi : Poly (fun c : Ctx D => (c.2.1,(c,([]:List ℕ)))) := by fun_prop
  exact (show Poly (fun z : Ctx D => (z.2.1.foldl (fun s i => push A b (s,i)) (z,[])).2) from comp (f:=Prod.snd) snd (comp ⟨F⟩ hi))

private theorem fold_eq (c : Ctx D) (todo : List ℕ) (sel : List ℕ) :
    (todo.foldl (fun s i => push A b (s,i)) (c,sel)).2 =
      sel ++ Dense.greedy (A c.1) (estimate A c) todo
        (fun j => b c.1 j+(sel.map (fun i => A c.1 i j)).sum) := by
  induction todo generalizing sel with
  | nil => simp [Dense.greedy]
  | cons i todo ih =>
    simp only [List.foldl_cons,push,Dense.greedy]
    split
    · change (todo.foldl (fun s i => push A b (s,i)) (c,sel++[i])).2 = _
      rw [ih]
      simp only [List.map_append,List.sum_append,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
        List.append_assoc,List.singleton_append]
      simp only [add_assoc]
    · exact ih sel

theorem run_eq (c : Ctx D) : run A b c =
    Dense.greedy (A c.1) (estimate A c) c.2.1 (b c.1) := by
  simpa only [run,List.map_nil,List.sum_nil,add_zero,List.nil_append] using fold_eq A b c c.2.1 []

end DualSepClusterLP.ScanDense
end

/- WordUtils -/
section
namespace DualSepClusterLP.SolverWords
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly

abbrev Word := List Bool
abbrev Mask := List Bool
abbrev Row := Mask × ℚ
abbrev GraphWord := List ℕ × Word

def mask {n : ℕ} (S : Finset (Fin n)) : Mask :=
  (List.finRange n).map (fun i => decide (i∈S))

@[fun_prop] theorem anyIds : Poly (fun bs : List Bool => bs.any id) :=
  ⟨(PolyProgram.identity encodeBool).listAny false⟩

@[fun_prop] theorem qsum : Poly (List.sum : List ℚ → ℚ) := ⟨PolyProgram.ratSum⟩

@[fun_prop] theorem boolEq : Poly (fun t : Bool × Bool => decide (t.1=t.2)) := ⟨PolyProgram.boolEq⟩

@[fun_prop] theorem and_comp {α : Type} [Coding α] {p q : α → Bool} (hp : Poly p) (hq : Poly q) :
    Poly (fun x => p x && q x) := comp Poly.bool_and (pair hp hq)

@[fun_prop] theorem boolEq_comp {α : Type} [Coding α] {p q : α → Bool} (hp : Poly p) (hq : Poly q) :
    Poly (fun x => decide (p x=q x)) := comp boolEq (pair hp hq)

@[fun_prop] theorem append_comp {α β : Type} [Coding α] [Coding β] [Inhabited β] {p q : α → List β}
    (hp : Poly p) (hq : Poly q) : Poly (fun x => p x ++ q x) := comp Poly.list_append (pair hp hq)

@[fun_prop] theorem cons_comp {α β : Type} [Coding α] [Coding β] {p : α → β} {q : α → List β}
    (hp : Poly p) (hq : Poly q) : Poly (fun x => p x :: q x) := comp Poly.list_cons (pair hp hq)

theorem range_fin (n : ℕ) : List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem <;> simp

theorem mask_at {n : ℕ} (S : Finset (Fin n)) (i : Fin n) :
    (mask S)[i.val]?.getD false = decide (i∈S) := by simp [mask,i.isLt]

end DualSepClusterLP.SolverWords
end

/- SolverWriter -/
section
namespace DualSepClusterLP.SolverWords
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly

@[fun_prop] theorem bits_poly : Poly Nat.bits := ⟨PolyProgram.natAsList⟩
def graphWord {n : ℕ} (G : Graph n) : GraphWord :=
  (List.range n,matrixBits (fun i j : Fin n => if i<j then G i j else false))

end DualSepClusterLP.SolverWords
end

/- WordZero -/
section
namespace DualSepClusterLP.SolverWords
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly
open Master (EquivalenceGraph block zeroList)

def adjacent (g : GraphWord) (i j : ℕ) : Bool :=
  decide (i=j) ||
  (if i<j then g.2[i*g.1.length+j]?.getD false else g.2[j*g.1.length+i]?.getD false)

@[fun_prop] theorem adjacent_poly : Poly (fun p : GraphWord × ℕ × ℕ => adjacent p.1 p.2.1 p.2.2) := by
  unfold adjacent; fun_prop

@[fun_prop] theorem adj_comp {α : Type} [Coding α] {g : α → GraphWord} {i j : α → ℕ}
    (hg : Poly g) (hi : Poly i) (hj : Poly j) :
    Poly (fun a => adjacent (g a) (i a) (j a)) := comp adjacent_poly (pair hg (pair hi hj))

private theorem flatten_cell {α β : Type*} (n : ℕ) (r : α → List β) (h : ∀ x,(r x).length=n)
    (xs : List α) (i j : ℕ) (hi : i<xs.length) (hj : j<n) :
    (xs.flatMap r)[i*n+j]? = (r xs[i])[j]? := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    rw [List.flatMap_cons]
    cases i with
    | zero =>
      simp only [Nat.zero_mul,zero_add,List.getElem_cons_zero]
      rw [List.getElem?_append_left (by simpa [h] using hj)]
    | succ i =>
      have hi' : i<xs.length := by simpa using hi
      rw [List.getElem?_append_right (by rw [h,Nat.add_mul,Nat.one_mul]; omega : (r x).length ≤ (i+1)*n+j)]
      rw [h]
      have he : (i+1)*n+j-n=i*n+j := by rw [Nat.add_mul]; omega
      rw [he,ih i hi']; simp

theorem matrix_at {n : ℕ} (G : Graph n) (i j : Fin n) :
    (matrixBits G)[i.val*n+j.val]?.getD false = G i j := by
  have hl (i : Fin n) : ((List.finRange n).map (G i)).length=n := by simp
  have hh := flatten_cell n (fun i : Fin n => (List.finRange n).map (G i)) hl
    (List.finRange n) i.val j.val (by simpa using i.isLt) j.isLt
  rw [matrixBits,hh]
  simp [i.isLt,j.isLt]

theorem adjacent_spec {n : ℕ} (G : Graph n) (i j : Fin n) :
    adjacent (graphWord G) i.val j.val = decide (Master.adj G i j) := by
  rcases lt_trichotomy i j with h|h|h
  · simp [graphWord,adjacent,Master.adj,h.ne,show i.val ≠ j.val from Nat.ne_of_lt h,h,min_eq_left h.le,max_eq_right h.le,matrix_at,Fin.ext_iff]
  · subst j; simp [graphWord,adjacent,Master.adj]
  · have hn := not_lt_of_ge h.le
    simp [graphWord,adjacent,Master.adj,h.ne',show i.val ≠ j.val from Nat.ne_of_gt h,hn,h,min_eq_right h.le,max_eq_left h.le,matrix_at,Fin.ext_iff]

end DualSepClusterLP.SolverWords
end

/- SepBase -/
section
namespace DualSepClusterLP.SepStructure
open Finset

def edges {n : ℕ} (G : Graph n) (A B : Finset (Fin n)) := ∑ v∈A, degree G B v

@[simp] theorem edge_diag {n : ℕ} (G : Graph n) (i : Fin n) : edge G i i = false := by simp [edge]
theorem edge_symm {n : ℕ} (G : Graph n) (i j : Fin n) : edge G i j = edge G j i := by
  rcases lt_trichotomy i j with h|rfl|h
  · simp [edge,h,not_lt_of_ge h.le]
  · rfl
  · simp [edge,h,not_lt_of_ge h.le]

def discrepancy {n : ℕ} (G : Graph n) (S : Finset (Fin n)) (v : Fin n) :=
  ((closed G v \ S) ∪ (S \ closed G v)).card

end DualSepClusterLP.SepStructure
end

/- SepWords -/
section
namespace DualSepClusterLP.SepWords
open SolverWords (GraphWord Word graphWord)
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly

abbrev Data := ℕ × (GraphWord × List ℚ)
def canon {n : ℕ} (t : ℕ) (G : Graph n) (q : Fin n → ℚ) : Data :=
  (t,graphWord G,(List.finRange n).map q)
def ids {n : ℕ} (S : Finset (Fin n)) : List ℕ :=
  ((List.finRange n).filter (fun i => decide (i∈S))).map Fin.val

def conn (x : Data) (i j : ℕ) := SolverWords.adjacent x.2.1 i j
def pos (x : Data) (i j : ℕ) := if i=j then false else conn x i j
def attr (x : Data) (i : ℕ) := x.2.2[i]?.getD 0
def members (x : Data) := x.2.1.1
def adjacentIds (x : Data) (A : List ℕ) (i : ℕ) := A.filter (fun j => conn x i j)
def openIds (x : Data) (A : List ℕ) (i : ℕ) := A.filter (fun j => pos x i j)
def uzone (x : Data) (s v : ℕ) :=
  let A := adjacentIds x (members x) v
  (members x).filter (fun i => decide (s ≤ 3*(adjacentIds x A i).length))
def uscore (x : Data) (U : List ℕ) (i : ℕ) : ℚ :=
  2*((openIds x U i).length:ℚ)-((openIds x (members x) i).length:ℚ)/2+attr x i
def near (x : Data) (s v h : ℕ) :=
  let U := uzone x s v
  U.filter (fun i => decide (uscore x U h < uscore x U i) ||
    (decide (uscore x U i = uscore x U h) && decide (i≤h)))
def seed (x : Data) (s v w : ℕ) :=
  (members x).filter (fun i => (conn x v i || conn x w i) &&
    decide ((adjacentIds x (members x) i).length ≤ (100*(x.1+1)+1)*s))
def win (x : Data) (s v w : ℕ) :=
  (members x).filter (fun i => decide (s ≤ 10*(adjacentIds x (seed x s v w) i).length))
def sign (x : Data) (i j : ℕ) : ℚ := if i=j then 0 else if pos x i j then -1 else 1
def unary (x : Data) (i : ℕ) : ℚ := ((openIds x (members x) i).length:ℚ)/2-attr x i

section
variable {α : Type} [Coding α] [Inhabited α] {x : α → Data} {i j s v h : α → ℕ} {A : α → List ℕ}

@[fun_prop] theorem conn_comp (hx : Poly x) (hi : Poly i) (hj : Poly j) : Poly (fun a => conn (x a) (i a) (j a)) := by unfold conn; fun_prop
@[fun_prop] theorem pos_comp (hx : Poly x) (hi : Poly i) (hj : Poly j) : Poly (fun a => pos (x a) (i a) (j a)) := by unfold pos; fun_prop
@[fun_prop] theorem attr_comp (hx : Poly x) (hi : Poly i) : Poly (fun a => attr (x a) (i a)) := by unfold attr; fun_prop
@[fun_prop] theorem members_comp (hx : Poly x) : Poly (fun a => members (x a)) := by unfold members; fun_prop
@[fun_prop] theorem adjacentIds_comp (hx : Poly x) (hA : Poly A) (hi : Poly i) :
    Poly (fun a => adjacentIds (x a) (A a) (i a)) := by unfold adjacentIds; apply list_filter <;> fun_prop
@[fun_prop] theorem openIds_comp (hx : Poly x) (hA : Poly A) (hi : Poly i) :
    Poly (fun a => openIds (x a) (A a) (i a)) := by unfold openIds; apply list_filter <;> fun_prop
@[fun_prop] theorem uzone_comp (hx : Poly x) (hs : Poly s) (hv : Poly v) :
    Poly (fun a => uzone (x a) (s a) (v a)) := by unfold uzone; apply list_filter <;> fun_prop
@[fun_prop] theorem uscore_comp (hx : Poly x) (hA : Poly A) (hi : Poly i) :
    Poly (fun a => uscore (x a) (A a) (i a)) := by unfold uscore; fun_prop
@[fun_prop] theorem near_comp (hx : Poly x) (hs : Poly s) (hv : Poly v) (hh : Poly h) :
    Poly (fun a => near (x a) (s a) (v a) (h a)) := by unfold near; apply list_filter <;> fun_prop
@[fun_prop] theorem seed_comp (hx : Poly x) (hs : Poly s) (hv : Poly v) (hh : Poly h) :
    Poly (fun a => seed (x a) (s a) (v a) (h a)) := by unfold seed; apply list_filter <;> fun_prop
@[fun_prop] theorem win_comp (hx : Poly x) (hs : Poly s) (hv : Poly v) (hh : Poly h) :
    Poly (fun a => win (x a) (s a) (v a) (h a)) := by unfold win; apply list_filter <;> fun_prop
@[fun_prop] theorem sign_comp (hx : Poly x) (hi : Poly i) (hj : Poly j) :
    Poly (fun a => sign (x a) (i a) (j a)) := by unfold sign; fun_prop
@[fun_prop] theorem unary_comp (hx : Poly x) (hi : Poly i) :
    Poly (fun a => unary (x a) (i a)) := by unfold unary; fun_prop
end
end DualSepClusterLP.SepWords
end

/- Candidate -/
section
namespace DualSepClusterLP.Dense
variable {ι : Type} [DecidableEq ι]

theorem value_map {α : Type} (A : ι → ι → ℚ) (b : ι → ℚ) (f : α → ι) (xs : List α) :
    value A b (xs.map f) = value (fun i j => A (f i) (f j)) (fun i => b (f i)) xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [value,row,List.map_map,Function.comp_def,ih]

theorem small_spec (U : List ι) (hu : U.Nodup) (keep : ι → Bool) :
    ∃ bits : List Bool, bits.length=U.length ∧ small U bits=U.filter keep := by
  refine ⟨U.map keep,List.length_map _,?_⟩
  apply List.filter_congr
  intro i hi
  obtain ⟨j,rfl⟩ := List.get_of_mem hi
  simp [hu.idxOf_getElem j.val j.isLt]

end DualSepClusterLP.Dense
namespace DualSepClusterLP.Dense
abbrev large_spec := @DualSepClusterLP.denseAffineApproximation
end DualSepClusterLP.Dense
end

/- Proposal -/
section
namespace DualSepClusterLP.Proposal
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly
open SepWords (Data)
abbrev Params := List ℕ × List Bool
abbrev Trial := Data × Params

def arg (z : Trial) (j : ℕ) := z.2.1[j]?.getD 0
def U (z : Trial) := SepWords.win z.1 (arg z 1) (arg z 2) (arg z 3)
def cfg (z : Trial) : ScanDense.Ctx Data := (z.1,U z,arg z 5,arg z 6,arg z 7,z.2.2)
def candidate (z : Trial) : List ℕ :=
  if arg z 0=0 then [arg z 2]
  else if arg z 0=1 then SepWords.near z.1 (arg z 1) (arg z 2) (arg z 4)
  else if arg z 0=2 then Dense.small (U z) z.2.2
  else ScanDense.run SepWords.sign SepWords.unary (cfg z)

@[fun_prop] theorem argP (j : ℕ) : Poly (fun z : Trial => arg z j) := by unfold arg; fun_prop
@[fun_prop] theorem UP : Poly U := by unfold U; fun_prop
@[fun_prop] theorem cfgP : Poly cfg := by unfold cfg; fun_prop
theorem smallP : Poly (fun z : Trial => Dense.small (U z) z.2.2) := by
  unfold Dense.small; apply list_filter <;> fun_prop
theorem candP : Poly candidate := by
  have hr := ScanDense.run_poly SepWords.sign SepWords.unary (by fun_prop) (by fun_prop)
  unfold candidate
  apply ite_prop (by fun_prop)
  · exact comp list_cons (pair (argP 2) (by fun_prop : Poly (fun _ : Trial => ([] : List ℕ))))
  · apply ite_prop (by fun_prop) (by fun_prop)
    exact ite_prop (by fun_prop) smallP (comp hr cfgP)

def args (mode s v w h p a b : ℕ) : List ℕ := [mode,s,v,w,h,p,a,b]

theorem single (x : Data) (v : ℕ) : candidate (x,args 0 0 v 0 0 0 0 0,[])=[v] := rfl
theorem near (x : Data) (s v h : ℕ) : candidate (x,args 1 s v 0 h 0 0 0,[])=SepWords.near x s v h := rfl
theorem small (x : Data) (s v w : ℕ) (ys : List Bool) :
    candidate (x,args 2 s v w 0 0 0 0,ys) = Dense.small (SepWords.win x s v w) ys := rfl
theorem large (x : Data) (s v w p a b : ℕ) (ys : List Bool) :
    candidate (x,args 3 s v w 0 p a b,ys) = ScanDense.run SepWords.sign SepWords.unary
      (x,SepWords.win x s v w,p,a,b,ys) := rfl

end DualSepClusterLP.Proposal
end

/- RawBridge -/
section
namespace DualSepClusterLP.ScanDense
variable {D : Type}

theorem estimate_eq (A : D → ℕ → ℕ → ℚ) (d : D) (U : List ℕ) (p a c : ℕ) (bits : List Bool) :
    estimate A (d,U,p,a,c,bits) = Dense.rawEstimate (A d) U bits.length p a c bits := by
  funext i
  unfold estimate Dense.rawEstimate
  dsimp only [pos]
  apply congrArg (fun q : ℚ => (p:ℚ)/bits.length*q)
  apply congrArg List.sum
  apply List.map_congr_left
  intro l _
  let z := (a*l+c)%p
  by_cases h : z<U.length
  · simp [z] at h
    by_cases hi : U.idxOf i < (a*l+c)%p <;> cases hb : bits[l]?.getD false <;> simp [h,hi,hb]
  · have hn : U.length≤(a*l+c)%p := Nat.le_of_not_gt h
    simp [Nat.not_lt_of_ge hn, List.getElem?_eq_none hn]

theorem candidate_eq [OAI.MetricKMedian.Binary.Automatic.Coding D] (A : D → ℕ → ℕ → ℚ) (b : D → ℕ → ℚ)
    (d : D) (U : List ℕ) (p a c : ℕ) (bits : List Bool) :
    run A b (d,U,p,a,c,bits) = Dense.greedy (A d) (Dense.rawEstimate (A d) U bits.length p a c bits) U (b d) := by
  rw [run_eq,estimate_eq]

end DualSepClusterLP.ScanDense
end

/- SepWordSpec -/
section
namespace DualSepClusterLP.SepWords
open Finset SepStructure

variable {n : ℕ} (t : ℕ) (G : Graph n) (q : Fin n → ℚ)

theorem ids_length (S : Finset (Fin n)) : (ids S).length = S.card := by
  let xs := (List.finRange n).filter (fun i => decide (i∈S))
  have hh : xs.toFinset=S := by ext i; simp [xs]
  have hn : xs.Nodup := (List.nodup_finRange n).filter _
  change (xs.map Fin.val).length = S.card
  rw [List.length_map,←List.toFinset_card_of_nodup hn,hh]

theorem ids_mem (S : Finset (Fin n)) (i : Fin n) : i.val ∈ ids S ↔ i∈S := by
  simp [ids,List.mem_map,Fin.ext_iff.symm]

theorem ids_nodup (S : Finset (Fin n)) : (ids S).Nodup :=
  ((List.nodup_finRange n).filter _).map Fin.val_injective

theorem member_spec : members (canon t G q) = ids (univ : Finset (Fin n)) := by
  simpa [members,canon,SolverWords.graphWord,ids] using SolverWords.range_fin n

theorem filtered (S T : Finset (Fin n)) (p : ℕ → Bool) (he : ∀ i : Fin n, i∈S ∧ p i.val=true ↔ i∈T) :
    (ids S).filter p = ids T := by
  simp only [ids,List.filter_map,List.filter_filter]
  congr 1; apply List.filter_congr
  intro i hi; apply Bool.eq_iff_iff.mpr
  simpa only [Bool.and_eq_true,Function.comp_apply,decide_eq_true_eq,and_comm] using he i

theorem conn_spec (i j : Fin n) : conn (canon t G q) i.val j.val = decide (j ∈ closed G i) := by
  change SolverWords.adjacent (SolverWords.graphWord G) i.val j.val = _
  rw [SolverWords.adjacent_spec]; congr 1; apply propext
  rcases lt_trichotomy i j with h|rfl|h
  · simp [Master.adj,closed,neighbors,edge,h,h.ne,h.ne',min_eq_left h.le,max_eq_right h.le]
  · simp [Master.adj,closed]
  · simp [Master.adj,closed,neighbors,edge,h,h.ne,h.ne',not_lt_of_ge h.le,min_eq_right h.le,max_eq_left h.le]

theorem pos_spec (i j : Fin n) : pos (canon t G q) i.val j.val = edge G i j := by
  by_cases h : i=j
  · subst j; simp [pos]
  · simp [pos,Fin.ext_iff.symm,h,conn_spec,closed,neighbors,Ne.symm h]

theorem adj_list (S : Finset (Fin n)) (i : Fin n) :
    adjacentIds (canon t G q) (ids S) i.val = ids (closed G i∩S) := by
  apply filtered; intro j; simp only [conn_spec,decide_eq_true_eq,mem_inter]; tauto

theorem open_list (S : Finset (Fin n)) (i : Fin n) :
    openIds (canon t G q) (ids S) i.val = ids (neighbors G i∩S) := by
  apply filtered; intro j; simp [pos_spec,neighbors,and_comm]

theorem zone_spec (s : ℕ) (v : Fin n) : uzone (canon t G q) s v.val = ids (Near.zone G s v) := by
  unfold uzone; rw [member_spec,adj_list,inter_univ]
  apply filtered; intro i
  rw [Near.zone,mem_filter]; simp only [mem_univ,true_and,decide_eq_true_eq,adj_list,ids_length,Near.count]

theorem score_spec (U : Finset (Fin n)) (i : Fin n) :
    uscore (canon t G q) (ids U) i.val = Near.score G q U i := by
  simp only [uscore,member_spec,open_list,ids_length,Near.score,degree]
  simp [attr,canon,i.isLt]

theorem near_spec (s : ℕ) (v h : Fin n) :
    near (canon t G q) s v.val h.val = ids (Near.candidate G q s v h) := by
  simp only [near,zone_spec,Near.candidate]; apply filtered
  intro i; simp [score_spec,Near.top]

theorem seed_spec (s : ℕ) (v w : Fin n) :
    seed (canon t G q) s v.val w.val =
      ids ((closed G v ∪ closed G w) ∩ eligible G t s) := by
  simp only [seed,member_spec]
  apply filtered; intro i
  simp only [conn_spec,adj_list,ids_length,inter_univ]
  simp [eligible,canon]
  intro _; exact decide_eq_true_iff

theorem win_spec (s : ℕ) (v w : Fin n) :
    win (canon t G q) s v.val w.val =
      ids (TwoPivot.window (closed G) (eligible G t s) s v w) := by
  simp only [win,member_spec,seed_spec]
  apply filtered; intro i
  simp [adj_list,ids_length,TwoPivot.window]

theorem unary_spec (i : Fin n) :
    unary (canon t G q) i.val = ((neighbors G i).card:ℚ)/2-q i := by
  simp only [unary,member_spec,open_list,ids_length,inter_univ]
  simp [attr,canon,i.isLt]

theorem sign_spec (i j : Fin n) :
    sign (canon t G q) i.val j.val = if i=j then 0 else if edge G i j then -1 else 1 := by
  simp [sign,pos_spec,Fin.ext_iff.symm]

end DualSepClusterLP.SepWords
end

/- CompressPrimal -/
section
namespace DualSepClusterLP.Compression

theorem twiceCost_eq {n : ℕ} (G : Graph n) (S : Finset (Fin n)) :
    (twiceCost G S : ℝ) = 2 * subsetCost G S := by
  simp only [twiceCost,subsetCost,Nat.cast_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  unfold twiceEntry
  split_ifs <;> norm_num

end DualSepClusterLP.Compression
end

/- WordCompression -/
section
namespace DualSepClusterLP.CheckWeights
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly
open SolverWords Compression

def twiceEdge (g : GraphWord) (S : Mask) (i j : ℕ) : ℚ :=
  let a := S[i]?.getD false
  let b := S[j]?.getD false
  if i<j then if g.2[i*g.1.length+j]?.getD false then
    (if decide (a=b) then 0 else 1) else (if a && b then 2 else 0)
  else 0

def cost (g : GraphWord) (S : Mask) : ℚ :=
  (g.1.map (fun i => (g.1.map (fun j => twiceEdge g S i j)).sum)).sum

@[fun_prop] theorem cost_poly : Poly (fun t : GraphWord × Mask => cost t.1 t.2) := by
  unfold cost
  apply Poly.comp (f:=List.sum) qsum
  apply list_map
  · apply Poly.comp (f:=List.sum) qsum
    apply list_map
    · unfold twiceEdge; fun_prop
    · fun_prop
  · fun_prop

private theorem edge_spec {n : ℕ} (G : Graph n) (S : Finset (Fin n)) (i j : Fin n) :
    twiceEdge (graphWord G) (mask S) i.val j.val = (twiceEntry G S i j : ℚ) := by
  simp only [twiceEdge,twiceEntry,graphWord,List.length_range,matrix_at,mask_at,Fin.val_fin_lt]
  by_cases h : i<j <;> by_cases a : i∈S <;> by_cases b : j∈S <;> cases hg : G i j <;>
    simp [h,a,b,hg]

theorem cost_spec {n : ℕ} (G : Graph n) (S : Finset (Fin n)) :
    cost (graphWord G) (mask S) = (twiceCost G S : ℚ) := by
  have h : (graphWord G).1 = (List.finRange n).map Fin.val := range_fin n
  simp only [cost,h,List.map_map,Function.comp_def,edge_spec]
  simp only [←List.ofFn_eq_map,List.sum_ofFn,twiceCost,Nat.cast_sum]

end DualSepClusterLP.CheckWeights
end

/- Front -/
section
namespace DualSepClusterLP.SolverFront
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly
open OAI.MetricKMedian.InputParser
open SolverWords (GraphWord Word Row graphWord)
abbrev Info := ℕ × GraphWord
def rest (xs : Word) : Word := xs.drop (width xs+1)
def ids (xs : Word) : List ℕ := List.range (xs.take (width xs)).length
def info (xs : Word) : Info := (width xs,ids (rest xs),rest (rest xs))
@[fun_prop] private theorem drop_comp {α : Type} [Coding α] {f : α → Word} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun p => (f p).drop (g p)) := comp drop_poly (pair hf hg)
@[fun_prop] private theorem take_comp {α : Type} [Coding α] {f : α → Word} {g : α → ℕ} (hf : Poly f) (hg : Poly g) :
    Poly (fun p => (f p).take (g p)) := comp take_poly (pair hf hg)

@[fun_prop] theorem rest_poly : Poly rest := by unfold rest; fun_prop
@[fun_prop] theorem ids_poly : Poly ids := by
  unfold ids
  exact comp (f:=fun v : Word => List.range v.length) list_indices (take_comp (by fun_prop : Poly (id : Word → Word)) width_poly)
@[fun_prop] theorem info_poly : Poly info := by unfold info; fun_prop
end DualSepClusterLP.SolverFront
end

/- WireTM -/
section
namespace DualSepClusterLP.WireTM
open OAI.MetricKMedian OAI.MetricKMedian.InputParser
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly

@[fun_prop] theorem take_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → ℕ} {g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => (g x).take (f x)) :=
  comp take_poly (pair hg hf)

@[fun_prop] theorem drop_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f : α → ℕ} {g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => (g x).drop (f x)) :=
  comp drop_poly (pair hg hf)

@[fun_prop] theorem append_comp {α β : Type} [Coding α] [Coding β] [Inhabited β]
    {f g : α → List β} (hf : Poly f) (hg : Poly g) : Poly (fun x => f x ++ g x) :=
  comp list_append (pair hf hg)


end DualSepClusterLP.WireTM
end

/- WordSearch -/
section
namespace DualSepClusterLP.WordSearch
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
abbrev W := List Bool

/-- Placing a one bit after a proposed certificate makes any finite string an initial segment of a binary integer. -/
def code (w : W) : ℕ := w.foldr Nat.bit 1

theorem code_pos (w : W) : 0 < code w := by
  induction w with
  | nil => decide
  | cons b w ih => cases b <;> simp [code,Nat.bit_val] at * <;> omega

theorem bits_code (w : W) : (code w).bits = w ++ [true] := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    change (Nat.bit b (code w)).bits=_
    rw [Nat.bits_append_bit _ _ (by have h := code_pos w; omega),ih]; rfl

variable {α β : Type} [Coding α] [Coding β]
def body (ok : α × W → Bool) (out : α × W → β) (a : α × ℕ) : β ⊕ (α × ℕ) :=
  if ok (a.1,a.2.bits) then .inl (out (a.1,a.2.bits)) else .inr (a.1,a.2+1)

noncomputable def program {ok : α × W → Bool} {out : α × W → β}
    (hc : Poly ok) (he : Poly out) :
    PolyProgram enc (encodeLoop (enc (α:=α × ℕ)) enc) (body ok out) := by
  open PolyProgram in
  let inp := fst (enc (α:=α)) Nat.bits
  let k := snd (enc (α:=α)) Nat.bits
  let word := inp.fanout (k.comp natAsList)
  let h := word.comp hc.program
  let o := (word.comp he.program).comp (injectLeft (enc (α:=α × ℕ)) enc)
  let inc := (k.fanout (constant enc Nat.bits 1)).comp natAdd
  let next := (inp.fanout inc).comp (injectRight (enc (α:=α × ℕ)) (enc (α:=β)))
  exact (ite h next o).congr _ (fun _ => rfl)

def stateSize (x : α) (K : ℕ) : ℕ := (enc (x,K)).length

theorem walk {ok : α × W → Bool} {out : α × W → β} (x : α)
    (K : ℕ) (hk : ok (x,K.bits) = true) (k : ℕ) (h : k≤K) :
    ∃ (j s : ℕ), j≤K ∧ s≤K-k+1 ∧ ok (x,j.bits)=true ∧
      BoundedRun enc (body ok out) (stateSize x K) s (x,k) (out (x,j.bits)) := by
  have hsize : (enc (x,k)).length ≤ stateSize x K := by
    change (encodePair enc Nat.bits (x,k)).length ≤ (encodePair enc Nat.bits (x,K)).length
    simp only [encodePair_length]; have := NatBinary.length_mono h; omega
  by_cases hy : ok (x,k.bits) = true
  · exact ⟨k,1,h,by omega,hy, .stop hsize (by simp [body,hy])⟩
  · have h' : k+1 ≤ K := by by_contra! hh; exact hy ((show k=K by omega) ▸ hk)
    obtain ⟨j,s,hj,hs,ho,hw⟩ := walk x K hk (k+1) h'
    exact ⟨j,s+1,hj,by omega,ho,.step hsize (by simp [body,hy]) hw⟩
termination_by K-k

noncomputable def start : PolyProgram enc (enc (α:=α × ℕ)) (fun x : α => (x,0)) :=
  (PolyProgram.identity (enc (α:=α))).fanout (PolyProgram.constant enc Nat.bits 0)

noncomputable def machine {ok : α × W → Bool} {out : α × W → β}
    (hc : Poly ok) (he : Poly out) : Machine :=
  Compose.machine (start (α:=α)).machine (Loop.machine (program hc he).machine)

theorem trace {ok : α × W → Bool} {out : α × W → β} (hc : Poly ok) (he : Poly out)
    (x : α) (K : ℕ) (hk : ok (x,K.bits)=true) :
    ∃ j t, j≤K ∧ ok (x,j.bits)=true ∧
      t ≤ (start (α:=α)).time.eval (enc x).length + 2*(enc ((x,0):α × ℕ)).length + 2 +
        (K+1)*(program hc he).passTime (stateSize x K) ∧
      Trace (machine hc he).step t ((machine hc he).initialCfg (enc x))
        ((machine hc he).finalCfg (enc (out (x,j.bits)))) := by
  obtain ⟨j,s,hj,hs,ho,hw⟩ := walk (out:=out) x K hk 0 (Nat.zero_le _)
  obtain ⟨T,hT,hr⟩ := (program hc he).run_loop hw
  let h := (start (α:=α)).outputs x
  have hl : Trace (start (α:=α)).machine.step h.steps ((start (α:=α)).machine.initialCfg (enc x))
      ((start (α:=α)).machine.finalCfg (enc ((x,0):α × ℕ))) := Trace.of_iterate h.evals_in_steps
  have res := Compose.run (start (α:=α)).machine (Loop.machine (program hc he).machine) hl hr
  refine ⟨j,_,hj,ho,?_,res⟩
  have := h.steps_le_m
  have hh := Nat.mul_le_mul_right ((program hc he).passTime (stateSize x K)) (by simpa using hs)
  omega

/-- The number of trials is exponential in the shortest accepted certificate length.
The time per trial is polynomial in that length and the original input length. -/
theorem verifier_clock {ok : α × W → Bool} {out : α × W → β} (hc : Poly ok) (he : Poly out) :
    ∃ (A b : ℕ), ∀ (x : α) (w : W), ok (x,w++[true])=true →
      ∃ j : ℕ, ok (x,j.bits)=true ∧ Nonempty (Turing.TM2OutputsInTime (machine hc he).tm
        (enc x) (some (enc (out (x,j.bits))))
        (2^(w.length+1)*A*((enc x).length+w.length+1)^b)) := by
  let init := start (α:=α)
  let p := program hc he
  let g : Polynomial ℕ := init.time + 2*(2*Polynomial.X+1) + 2 +
    (p.time + 2*p.sizeBound+3).comp (2*Polynomial.X+2)
  have clk (P : Polynomial ℕ) : ∃ A b : ℕ, ∀ m, P.eval m ≤ A*(m+1)^b := by
    induction P using Polynomial.induction_on' with
    | monomial k a => exact ⟨a,k,fun m => by simp only [Polynomial.eval_monomial]; gcongr; omega⟩
    | add P Q hp hq =>
      obtain ⟨A,b,hA⟩ := hp; obtain ⟨C,d,hC⟩ := hq
      refine ⟨A+C,b+d,fun m => ?_⟩
      rw [Polynomial.eval_add,add_mul]
      exact (Nat.add_le_add (hA m) (hC m)).trans (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))))
  obtain ⟨A,b,hab⟩ := clk g
  refine ⟨A,b,?_⟩; intro x w hw
  let K := code w
  have hbits : K.bits = w++[true] := bits_code w
  obtain ⟨j,t,hj,hv,ht,hr⟩ := trace hc he x K (by rwa [hbits])
  let m := (enc x).length+w.length
  have hk : K+1 ≤ 2^(w.length+1) := by
    have h := Nat.lt_size_self K
    rwa [←Nat.size_eq_bits_len,hbits,List.length_append,List.length_singleton] at h
  have hi : (enc ((x,0):α × ℕ)).length ≤ 2*m+1 := by
    change (encodePair enc Nat.bits (x,0)).length ≤ _
    simp [encodePair_length,m]
  have hs : stateSize x K ≤ 2*m+2 := by
    change (encodePair enc Nat.bits (x,K)).length ≤ _
    simp [encodePair_length,hbits,m]; omega
  have hxm : (enc x).length ≤ m := Nat.le_add_right _ _
  have h := ht.trans (Nat.add_le_add (Nat.add_le_add_right
    (Nat.add_le_add (polynomial_eval_mono init.time hxm)
       (Nat.mul_le_mul_left 2 hi)) 2)
    (Nat.mul_le_mul hk (show p.passTime (stateSize x K) ≤
      (p.time+2*p.sizeBound+3).eval (2*m+2) by
      simp only [PolyProgram.passTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
      gcongr <;> apply polynomial_eval_mono _ hs)))
  have hb : t≤ 2^(w.length+1)*g.eval m := by
    simp only [g,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_ofNat,Polynomial.eval_one]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat] at h
    have hpos : 0<2^(w.length+1) := by positivity
    nlinarith
  refine ⟨j,hv,⟨⟨⟨_,hr.iterate_eq⟩,?_⟩⟩⟩
  exact hb.trans (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (hab m))

end DualSepClusterLP.WordSearch
end

/- SearchIO -/
section
namespace DualSepClusterLP.SepSearch
open OAI.MetricKMedian OAI.MetricKMedian.InputParser OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly
open SolverWords (Word GraphWord graphWord mask)

abbrev Data := ℕ × (GraphWord × List ℚ)
abbrev Params := List ℕ × List Bool
abbrev Candidate := Data × Params → List ℕ
def data {n : ℕ} (G : Graph n) (q : Fin n → ℚ) (t : ℕ) : Data :=
  (t,graphWord G,(List.finRange n).map q)
def setOfIds {n : ℕ} (xs : List ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val ∈ xs)

def complete (c : Candidate) (C d : ℕ) (Good : (t n : ℕ) → Graph n → (Fin n → ℚ) → Prop) : Prop :=
  ∀ t n (G : Graph n) (q : Fin n → ℚ), ¬Good t n G q → ∃ p : Params,
    p.1.length=8 ∧ (∀ i∈p.1,i≤2*(n+1)) ∧ p.2.length≤C*(t+1)^d ∧
    let S := setOfIds (c (data G q t,p))
    subsetCost G S < ∑ i∈S,(q i:ℝ)

def readData (w : Word) : Data :=
  let z := SolverFront.info w
  let g := z.2
  let m := g.1.length*g.1.length
  (z.1,(g.1,g.2.take m),(parse ratRead (g.1.map (fun _ => ()),g.2.drop m)).1)

@[fun_prop] theorem readData_poly : Poly readData := by
  have hp : Poly (parse ratRead) := ⟨parseProgram ratRead ratRead_poly.program ratRead_rest_length⟩
  unfold readData; fun_prop

theorem readData_spec {n : ℕ} (t : ℕ) (G : Graph n) (q : Fin n → ℚ) :
    readData (separationInput t G q) = data G q t := by
  let m := (graphWord G).2
  have hm : m.length=n*n := by simp [m,graphWord,matrixBits,List.length_flatMap,List.map_const']
  have hid : SolverFront.info (separationInput t G q) = (t,List.range n,m++pricesBits q) := by
    have ha (k : ℕ) (w : Word) : SolverFront.rest (List.replicate k true ++ false::w) = w := by
      simp [SolverFront.rest,prefix_width,List.drop_append]
    have hb (k : ℕ) (w : Word) : SolverFront.ids (List.replicate k true ++ false::w)=List.range k := by
      simp [SolverFront.ids,prefix_width]
    simp only [SolverFront.info,separationInput,graphInput,List.append_assoc,List.cons_append,List.nil_append,
      prefix_width,ha,hb]
    rfl
  have hr (x : ℚ) (s : Word) : ratRead (priceBits x ++ s)=(x,s) := ratRead_append x s
  have he := parse_encoded ratRead priceBits hr ((List.finRange n).map q) []
  simp only [List.length_map,List.length_finRange,List.append_nil] at he
  change _ = (t,(List.range n,m),(List.finRange n).map q)
  simp only [readData,hid,List.length_range,←hm,List.take_left,List.drop_left,List.map_const']
  have hh := congrArg Prod.fst he
  simp only [←List.flatMap_def,List.flatMap_map] at hh
  rw [show (parse ratRead (List.replicate n (), pricesBits q)).1 = _ from hh]

def makeMask (x : List ℕ × List ℕ) : Word := x.1.map (fun i => (x.2.map (fun j => decide (i=j))).any id)
@[fun_prop] theorem makeMask_poly : Poly makeMask := by
  unfold makeMask
  apply list_map
  · apply Poly.comp SolverWords.anyIds
    apply list_map <;> fun_prop
  · fun_prop

theorem makeMask_spec {n : ℕ} (a : List ℕ) : makeMask (List.range n,a)=mask (setOfIds a : Finset (Fin n)) := by
  unfold makeMask mask
  rw [SolverWords.range_fin,List.map_map]
  apply List.map_congr_left
  intro i _
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply,List.any_eq_true,List.mem_map,id_eq,decide_eq_true_eq,
    setOfIds,Finset.mem_filter,Finset.mem_univ,true_and]
  aesop


def price (x : Data × List ℕ) : ℚ :=
  let m := makeMask (x.1.2.1.1,x.2)
  (x.1.2.1.1.map (fun i => if m[i]?.getD false then x.1.2.2[i]?.getD 0 else 0)).sum

@[fun_prop] theorem price_poly : Poly price := by
  unfold price
  apply Poly.comp SolverWords.qsum
  apply list_map <;> fun_prop

theorem price_spec {n : ℕ} (t : ℕ) (G : Graph n) (q : Fin n → ℚ) (a : List ℕ) :
    price (data G q t,a) = ∑ i∈setOfIds a,q i := by
  change ((List.range n).map (fun i => if (makeMask (List.range n,a))[i]?.getD false then
      ((List.finRange n).map q)[i]?.getD 0 else 0)).sum = _
  rw [makeMask_spec,SolverWords.range_fin,List.map_map,←List.ofFn_eq_map,List.sum_ofFn]
  simp [SolverWords.mask_at]


def valid (x : Data × List ℕ) : Bool :=
  decide (CheckWeights.cost x.1.2.1 (makeMask (x.1.2.1.1,x.2)) < 2*price x)
@[fun_prop] theorem valid_poly : Poly valid := by
  unfold valid
  have h : Poly (fun x : Data × List ℕ => CheckWeights.cost x.1.2.1 (makeMask (x.1.2.1.1,x.2))) :=
    comp (f:=fun u : GraphWord × Word => CheckWeights.cost u.1 u.2) (g:=fun x : Data × List ℕ => (x.1.2.1,makeMask (x.1.2.1.1,x.2))) CheckWeights.cost_poly (by fun_prop)
  fun_prop

theorem valid_spec {n : ℕ} (t : ℕ) (G : Graph n) (q : Fin n → ℚ) (a : List ℕ) :
    valid (data G q t,a)=true ↔ subsetCost G (setOfIds a)< ∑ i∈setOfIds a,(q i:ℝ) := by
  change decide (CheckWeights.cost (graphWord G) (makeMask (List.range n,a)) < 2*price (data G q t,a)) = true ↔ _
  rw [makeMask_spec,CheckWeights.cost_spec,price_spec,decide_eq_true_eq]
  rw [←Rat.cast_lt (K:=ℝ)]
  simp only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_ofNat,Rat.cast_sum,Compression.twiceCost_eq,
    mul_lt_mul_iff_right₀ (by norm_num : (0:ℝ)<2)]

end DualSepClusterLP.SepSearch
end

/- SepStructure -/
section
namespace DualSepClusterLP.SepStructure
open Finset

private def hit {n : ℕ} (G : Graph n) (S : Finset (Fin n)) (i j : Fin n) : ℝ :=
  if i∈S ∧ (j ∈ closed G i ↔ j∉S) then 1 else 0

private theorem upper {n : ℕ} (f : Fin n → Fin n → ℝ) (hd : ∀ i, f i i = 0) :
    (∑ i, ∑ j, if i<j then f i j+f j i else 0) = ∑ i, ∑ j, f i j := by
  have hs : (∑ i, ∑ j, if i<j then f j i else 0) =
      ∑ i : Fin n, ∑ j : Fin n, if j < i then f i j else 0 := Finset.sum_comm
  simp_rw [ite_add_zero,Finset.sum_add_distrib]
  rw [hs,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro j _
  rcases lt_trichotomy i j with h|rfl|h
  · simp [h,not_lt_of_ge h.le]
  · simp [hd]
  · simp [h,not_lt_of_ge h.le]

theorem discrepancy_sum {n : ℕ} (G : Graph n) (S : Finset (Fin n)) :
    (∑ v∈S, (discrepancy G S v : ℝ)) = 2*subsetCost G S := by
  classical
  have hd (i : Fin n) : hit G S i i = 0 := by
    by_cases h : i∈S <;> simp [hit,h,closed]
  have hu := upper (hit G S) hd
  have hr : 2*subsetCost G S = ∑ i,∑ j, if i<j then hit G S i j + hit G S j i else 0 := by
    unfold subsetCost
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro j _
    by_cases hj : i < j
    · have hji := not_lt_of_ge hj.le
      cases e : G i j <;> by_cases a : i∈S <;> by_cases b : j∈S <;>
        norm_num [hj,hji,hit,closed,neighbors,edge,hj.ne,hj.ne',e,a,b]
    · simp [hj]
  rw [hr,hu]
  rw [← Finset.sum_subset (show S ⊆ Finset.univ from Finset.subset_univ S)]
  · apply Finset.sum_congr rfl; intro v hv
    let D := (closed G v \ S) ∪ (S \ closed G v)
    have hD : (∑ j, if j∈D then (1:ℝ) else 0) = (D.card:ℝ) := by simp
    change (D.card:ℝ) = _
    rw [←hD]
    apply Finset.sum_congr rfl; intro j _
    by_cases hx : j∈closed G v <;> by_cases hy : j∈S <;> simp [D,hit,hv,hx,hy]
  · intro v _ h
    simp [hit,h]

end DualSepClusterLP.SepStructure
end

/- BaseCounts -/
section
namespace DualSepClusterLP.SepStructure
open Finset

variable {n : ℕ} (G : Graph n)

theorem degree_sum (A : Finset (Fin n)) (i : Fin n) :
    degree G A i = ∑ j∈A, if edge G i j then 1 else 0 := by
  have h : (neighbors G i ∩ A) = A.filter (fun j => edge G i j) := by
    ext j; simp [neighbors,and_comm]
  rw [degree,h,Finset.card_filter]

theorem edges_symm (A B : Finset (Fin n)) : edges G A B = edges G B A := by
  simp only [edges,degree_sum]
  rw [sum_comm]; apply sum_congr rfl
  intro i _; apply sum_congr rfl; intro j _; rw [edge_symm G j i]

theorem disc_counts (S : Finset (Fin n)) (i : Fin n) (hi : i∈S) :
    discrepancy G S i + 2*degree G S i + 1 = S.card+degree G univ i := by
  have hni : i∉neighbors G i := by simp [neighbors]
  have he : closed G i ∩ S = insert i (neighbors G i ∩ S) := by ext j; by_cases h : j=i <;> simp [closed,h,hi]
  have hd : Disjoint (closed G i \ S) (S \ closed G i) := Finset.disjoint_left.mpr (fun _ hx hy => (mem_sdiff.mp hx).2 (mem_sdiff.mp hy).1)
  have h1 := card_sdiff_add_card_inter (closed G i) S
  have h2 := card_sdiff_add_card_inter S (closed G i)
  rw [inter_comm S,he,card_insert_of_notMem (by simp [hni])] at h2
  have hc : (closed G i).card = (neighbors G i).card+1 := card_insert_of_notMem hni
  rw [he,card_insert_of_notMem (by simp [hni]),hc] at h1
  simp only [discrepancy,card_union_of_disjoint hd,degree,inter_univ]
  omega

end DualSepClusterLP.SepStructure
end

/- NearCounts -/
section
namespace DualSepClusterLP.SepStructure
open Finset
variable {n : ℕ} (G : Graph n)

theorem cost_quad (S : Finset (Fin n)) :
    2*subsetCost G S = (S.card:ℝ)*((S.card:ℝ)-1)+(edges G S univ:ℝ)-2*(edges G S S:ℝ) := by
  have h := sum_congr (s₁:=S) (s₂:=S) rfl (fun i hi => disc_counts G S i hi)
  simp only [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul,mul_one] at h
  have hq := congrArg (fun a : ℕ => (a:ℝ)) h
  push_cast at hq
  rw [discrepancy_sum] at hq
  simp only [edges,Nat.cast_sum]
  nlinarith

end DualSepClusterLP.SepStructure
end

/- DenseGap -/
section
namespace DualSepClusterLP.SepStructure
open Finset

private theorem cross_union {n : ℕ} (G : Graph n) (A B T : Finset (Fin n)) (hd : Disjoint A B) :
    edges G (A∪B) T = edges G A T + edges G B T := by simp [edges,sum_union hd]

private theorem union_cross {n : ℕ} (G : Graph n) (A B T : Finset (Fin n)) (hd : Disjoint A B) :
    edges G T (A∪B) = edges G T A + edges G T B := by
  simpa only [edges_symm G T] using cross_union G A B T hd

theorem partition_identity {n : ℕ} (G : Graph n) (A B : Finset (Fin n)) (hd : Disjoint A B) :
    subsetCost G A + subsetCost G B = subsetCost G (A∪B) + 2*(edges G A B:ℝ) - A.card*B.card := by
  have h := cost_quad G (A∪B)
  rw [Finset.card_union_of_disjoint hd,cross_union G A B univ hd,
    cross_union G A B (A∪B) hd,union_cross G A B A hd,union_cross G A B B hd,edges_symm G B A] at h
  push_cast at h
  nlinarith [cost_quad G A,cost_quad G B]

end DualSepClusterLP.SepStructure
end

/- GraphValue -/
section
namespace DualSepClusterLP.Dense
open SepStructure Finset

def sign {n : ℕ} (G : Graph n) (i j : Fin n) : ℚ :=
  if i=j then 0 else if edge G i j then -1 else 1

def unary {n : ℕ} (G : Graph n) (q : Fin n → ℚ) (i : Fin n) : ℚ :=
  ((neighbors G i).card:ℚ)/2-q i

theorem sign_bound {n : ℕ} (G : Graph n) (i j : Fin n) : |sign G i j|≤1 := by
  unfold sign; split_ifs <;> norm_num

theorem singleton_cost {n : ℕ} (G : Graph n) (i : Fin n) :
    subsetCost G {i} = ((neighbors G i).card:ℝ)/2 := by
  have h := cost_quad G {i}
  have hn : i ∉ neighbors G i := by simp [neighbors]
  have e : (neighbors G i) ∩ {i} = ∅ := by ext j; simp; rintro hj rfl; exact hn hj
  simp only [Finset.card_singleton,Nat.cast_one,sub_self,mul_zero,zero_add,edges,sum_singleton,
    degree,inter_univ,e,card_empty,Nat.cast_zero,sub_zero] at h
  linarith

private theorem toSetSum {α : Type} [DecidableEq α] (f : α → ℚ) (xs : List α) (h : xs.Nodup) :
    (xs.map f).sum=∑ x∈xs.toFinset,f x := by
  induction xs with
  | nil => simp
  | cons i xs ih =>
    have ha := List.nodup_cons.mp h
    simp [ha,ih ha.2]

private theorem row_sign {n : ℕ} (G : Graph n) (i : Fin n) (xs : List (Fin n)) (h : xs.Nodup) (hi : i∉xs) :
    row (sign G) i xs = (xs.toFinset.card:ℚ)-2*(degree G xs.toFinset i : ℚ) := by
  rw [row,toSetSum _ xs h]
  have eq (j : Fin n) (hj : j∈xs.toFinset) :
      sign G i j = 1-2*(if j∈neighbors G i then (1:ℚ) else 0) := by
    have ne : i≠j := by rintro rfl; exact hi (List.mem_toFinset.mp hj)
    cases hg : edge G i j <;> norm_num [sign,ne,neighbors,hg]
  rw [Finset.sum_congr rfl eq,Finset.sum_sub_distrib,←Finset.mul_sum,←Finset.sum_filter]
  simp [degree,Finset.filter_mem_eq_inter,inter_comm]

theorem value_graph {n : ℕ} (G : Graph n) (q : Fin n → ℚ) (xs : List (Fin n)) (h : xs.Nodup) :
    (value (sign G) (unary G q) xs : ℝ) = subsetCost G xs.toFinset - ∑ i∈xs.toFinset,(q i:ℝ) := by
  induction xs with
  | nil => simp [value,subsetCost]
  | cons i xs ih =>
    obtain ⟨hi,hd⟩ := List.nodup_cons.mp h
    have hn : i ∉ xs.toFinset := by simpa using hi
    have ed := partition_identity G {i} xs.toFinset (by simpa)
    rw [singleton_cost] at ed
    simp only [edges,sum_singleton,singleton_union,card_singleton,Nat.cast_one,one_mul] at ed
    simp only [value,List.toFinset_cons,Finset.sum_insert hn,row_sign G i xs hd hi,unary,
      Rat.cast_add,Rat.cast_sub,Rat.cast_div,Rat.cast_natCast,Rat.cast_mul,Rat.cast_ofNat,ih hd]
    linarith

end DualSepClusterLP.Dense
end

/- SepObj -/
section
namespace DualSepClusterLP.SepWords
open Finset
variable {n : ℕ} (t : ℕ) (G : Graph n) (q : Fin n → ℚ)

theorem set_ids (S : Finset (Fin n)) : SepSearch.setOfIds (ids S) = S := by
  ext i; simp [SepSearch.setOfIds,ids_mem]

theorem set_single (i : Fin n) : SepSearch.setOfIds [i.val] = ({i} : Finset (Fin n)) := by
  ext j; simp [SepSearch.setOfIds,Fin.ext_iff]

theorem filter_ids (U S : Finset (Fin n)) (h : S⊆U) :
    (ids U).filter (fun j => decide (j ∈ ids S)) = ids S := by
  apply filtered
  intro i; simp [ids_mem]; exact fun _ => h ‹_›

theorem num_lt (W : Finset (Fin n)) {k : ℕ} (h : k∈ ids W) : k<n := by
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp h
  exact i.isLt

theorem value_raw (Y : List ℕ) (hn : Y.Nodup) (hY : ∀ i∈Y, i<n) :
    (Dense.value (sign (canon t G q)) (unary (canon t G q)) Y : ℝ) =
      Near.lag G q (SepSearch.setOfIds Y) := by
  have hf : ∃ xs : List (Fin n), xs.map Fin.val = Y := by
    clear hn
    induction Y with
    | nil => exact ⟨[],rfl⟩
    | cons i ys ih =>
      obtain ⟨xs,hxs⟩ := ih (fun j hj => hY j (List.mem_cons_of_mem _ hj))
      exact ⟨⟨i,hY _ (by simp)⟩::xs,by simp [hxs]⟩
  obtain ⟨xs,rfl⟩ := hf
  have hd : xs.Nodup := hn.of_map _
  have he : SepSearch.setOfIds (xs.map Fin.val) = xs.toFinset := by
    ext i; simp [SepSearch.setOfIds,Fin.ext_iff.symm]
  rw [he]
  have hv : Dense.value (sign (canon t G q)) (unary (canon t G q)) (xs.map Fin.val) =
      Dense.value (Dense.sign G) (Dense.unary G q) xs := by
    clear hn hY hd he
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      simp only [List.map_cons,Dense.value,Dense.row,List.map_map,Function.comp_def,
        sign_spec,unary_spec,Dense.unary,ih]; rfl
  rw [hv]
  exact Dense.value_graph G q xs hd

theorem ids_value (S : Finset (Fin n)) :
    (Dense.value (sign (canon t G q)) (unary (canon t G q)) (ids S) : ℝ) = Near.lag G q S := by
  rw [value_raw _ _ _ _ (ids_nodup _) (fun _ hi => num_lt _ hi),set_ids]

theorem sign_bound (x : Data) (i j : ℕ) : |sign x i j| ≤ 1 := by unfold sign; split_ifs <;> norm_num

end DualSepClusterLP.SepWords
end

/- TrialSpec -/
section
namespace DualSepClusterLP.Proposal
open Finset
open SepCheck
open SepWords (ids ids_length ids_nodup set_ids set_single sign_bound ids_value value_raw)

def K := (25600*(20*101^2)^2)^2

private theorem bit_cap (t : ℕ) : (accuracy t)^2 ≤ K*(t+1)^12 := by
  have hs : scale t ≤ 101*(t+1) := by unfold scale; omega
  have hm : accuracy t ≤ (25600*(20*101^2)^2)*(t+1)^6 := calc
    _ ≤ 25600*(t+1)^2*(20*(101*(t+1))^2)^2 := by unfold accuracy growth; gcongr
    _ = _ := by ring
  calc
    _ ≤ ((25600*(20*101^2)^2)*(t+1)^6)^2 := Nat.pow_le_pow_left hm _
    _ = _ := by unfold K;ring

private theorem bounded {n mode s v w h p a b : ℕ}
    (hm : mode ≤ 2*(n+1)) (hs : s ≤ 2*(n+1)) (hv : v ≤ 2*(n+1))
    (hw : w ≤ 2*(n+1)) (hh : h ≤ 2*(n+1)) (hp : p ≤ 2*(n+1))
    (ha : a ≤ 2*(n+1)) (hb : b ≤ 2*(n+1)) :
    ∀ j∈args mode s v w h p a b, j≤2*(n+1) := by
  simp only [args,List.mem_cons,List.not_mem_nil,or_false]
  rintro j (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) <;> assumption

theorem complete : SepSearch.complete candidate K 12 (fun t _ G q => Checks t G q) := by
  intro t n G q hbad
  let x := SepWords.canon t G q
  let bad (Y : List ℕ) := Near.lag G q (SepSearch.setOfIds Y) < 0
  have ret (ns bs) (hlen : List.length ns=8) (hb : ∀ j∈ns,j≤2*(n+1))
      (hbl : List.length bs≤K*(t+1)^12) (hneg : bad (candidate (x,ns,bs))) :
      ∃ p : SepSearch.Params, p.1.length=8 ∧ (∀ j∈p.1,j≤2*(n+1)) ∧
        p.2.length ≤ K*(t+1)^12 ∧
        (let S := SepSearch.setOfIds (candidate (SepSearch.data G q t,p))
         subsetCost G S < ∑ i∈S, (q i:ℝ)) := by
    refine ⟨(ns,bs),hlen,hb,hbl,?_⟩
    change subsetCost G _ < _
    exact sub_neg.mp hneg
  by_cases singleton : ∀ v,(q v:ℝ) ≤ subsetCost G {v}
  · by_cases hnear : ∀ s ≤ n, ∀ v h : Fin n, 0 ≤ Near.lag G q (Near.candidate G q s v h)
    · have hf : ¬ ∀ s ≤ n, ∀ v w : Fin n, ∀ X ⊆ localize t G s v w,
          0 ≤ (accuracy t:ℝ)*Near.lag G q X+2*((localize t G s v w).card:ℝ)^2 :=
        fun h => hbad ⟨singleton,hnear,h⟩
      push_neg at hf
      obtain ⟨s,hs,v,w,X,hX,hXbad⟩ := hf
      let W := localize t G s v w
      let U := ids W
      let m := accuracy t
      have hm : 0 < m := by apply Nat.mul_pos (Nat.mul_pos (by decide) (pow_pos (by omega) _))
                                             (pow_pos (by unfold growth scale; positivity) _)
      have hmr : 0 < (m:ℝ) := by exact_mod_cast hm
      have hwin : SepWords.win x s v.val w.val = U := SepWords.win_spec t G q s v w
      have hlen : U.length=W.card := ids_length _
      have hN : U.length≤n := by rw [hlen]; exact (Finset.card_le_univ W).trans_eq (Fintype.card_fin n)
      let keep := fun j : ℕ => decide (j∈ids X)
      have htarg : U.filter keep = ids X := SepWords.filter_ids W X hX
      have hval : Near.lag G q X < 0 := by
        by_contra! hz
        exact hXbad.not_ge (add_nonneg (mul_nonneg hmr.le hz) (by positivity))
      by_cases hl : U.length ≤ m^2
      · obtain ⟨bs,hb,hy⟩ := Dense.small_spec U (ids_nodup _) keep
        apply ret (args 2 s v.val w.val 0 0 0 0) bs rfl (bounded (n:=n) (by omega) (by omega)
          (by have := v.isLt;omega) (by have := w.isLt;omega) (by omega) (by omega) (by omega) (by omega))
          ((hb.le.trans hl).trans (bit_cap t))
        change Near.lag G q (SepSearch.setOfIds _) < 0
        rw [small,hwin,hy,htarg,set_ids]; exact hval
      · obtain ⟨p,a,b,bs,hp,hpmax,ha,hb,hbs,hobj⟩ := Dense.large_spec U (ids_nodup _) (SepWords.sign x)
          (SepWords.unary x) keep (fun i _ j _ => sign_bound x i j) m hm (lt_of_not_ge hl)
        let Y := Dense.greedy (SepWords.sign x) (Dense.rawEstimate (SepWords.sign x) U (m^2) p a b bs) U (SepWords.unary x)
        have hsub : Y.Sublist U := Dense.greedy_sublist _ _ _ _
        have hY := value_raw t G q Y (hsub.nodup (ids_nodup _)) (fun i hi => SepWords.num_lt W (hsub.subset hi))
        have hR : (Dense.value (SepWords.sign x) (SepWords.unary x) Y : ℝ) ≤
            (Dense.value (SepWords.sign x) (SepWords.unary x) (ids X):ℝ)+2*(U.length:ℝ)^2/m := by
          rw [htarg] at hobj
          have hh := (Rat.cast_le (K:=ℝ)).mpr hobj
          push_cast at hh
          exact hh
        rw [hY,ids_value,hlen] at hR
        have hLt : Near.lag G q X + 2*(W.card:ℝ)^2/m < 0 := by
          have hv : 2*(W.card:ℝ)^2/m < -Near.lag G q X := by
            apply (div_lt_iff₀ hmr).mpr
            change (m:ℝ)*Near.lag G q X+2*(W.card:ℝ)^2<0 at hXbad
            linarith
          linarith
        apply ret (args 3 s v.val w.val 0 p a b) bs rfl (bounded (n:=n)
          (by have := v.isLt;omega) (by omega) (by have := v.isLt;omega) (by have := w.isLt;omega)
          (by omega) (by omega) (by omega) (by omega)) (hbs.le.trans (bit_cap t))
        have hscan : ScanDense.run SepWords.sign SepWords.unary (x,U,p,a,b,bs)=Y := by
          rw [ScanDense.candidate_eq,hbs]
        change Near.lag G q (SepSearch.setOfIds _) < 0
        rw [large,hwin,hscan]; exact hR.trans_lt hLt
    · push_neg at hnear
      obtain ⟨s,hs,v,h,hh⟩ := hnear
      apply ret (args 1 s v.val 0 h.val 0 0 0) [] rfl (bounded
        (by omega) (by omega) (by have := v.isLt;omega) (by omega) (by have := h.isLt;omega)
        (by omega) (by omega) (by omega)) (by simp)
      change Near.lag G q (SepSearch.setOfIds _) < 0
      rw [near,SepWords.near_spec,set_ids]; exact hh
  · push_neg at singleton
    obtain ⟨v,hv⟩ := singleton
    apply ret (args 0 0 v.val 0 0 0 0 0) [] rfl (bounded
      (by omega) (by omega) (by have := v.isLt;omega) (by omega) (by omega) (by omega) (by omega) (by omega)) (by simp)
    change Near.lag G q (SepSearch.setOfIds _) < 0
    rw [single,set_single]; simpa only [Near.lag,sum_singleton,sub_neg] using hv

end DualSepClusterLP.Proposal
end

/- TimeBudget -/
section
namespace DualSepClusterLP.TimeBudget

def Bound (f : ℕ → ℕ → ℕ) : Prop :=
  ∃ A a b : ℕ, ∀ t n, f t n ≤ 2^(A*(t+1)^a)*(n+1)^b

theorem mono {f g : ℕ → ℕ → ℕ} (hf : Bound f) (h : ∀ t n, g t n ≤ f t n) : Bound g := by
  obtain ⟨A,a,b,hh⟩ := hf
  exact ⟨A,a,b,fun t n => (h t n).trans (hh t n)⟩

theorem const (c : ℕ) : Bound (fun _ _ => c) :=
  ⟨c,0,0,fun _ _ => by simpa using (Nat.lt_two_pow_self (n:=c)).le⟩

theorem param : Bound (fun t _ => t) :=
  ⟨1,1,0,fun t _ => by simpa using (Nat.le_succ t).trans (Nat.lt_two_pow_self (n:=t+1)).le⟩

theorem size : Bound (fun _ n => n) := ⟨0,0,1,fun _ n => by simp⟩

private theorem merge_exp (A C a c t : ℕ) :
    A*(t+1)^a+C*(t+1)^c ≤ (A+C)*(t+1)^(a+c) := by
  rw [add_mul]
  apply Nat.add_le_add <;> apply Nat.mul_le_mul_left <;> apply Nat.pow_le_pow_right (by omega) <;> omega

theorem mul {f g : ℕ → ℕ → ℕ} (hf : Bound f) (hg : Bound g) : Bound (fun t n => f t n*g t n) := by
  obtain ⟨A,a,b,hh⟩ := hf
  obtain ⟨C,c,d,hj⟩ := hg
  refine ⟨A+C,a+c,b+d,fun t n => (Nat.mul_le_mul (hh t n) (hj t n)).trans ?_⟩
  calc
    _ = (2^(A*(t+1)^a)*2^(C*(t+1)^c))*((n+1)^b*(n+1)^d) := by ac_rfl
    _ ≤ _ := by
      rw [← pow_add,← pow_add]
      exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (merge_exp A C a c t))

theorem succ {f : ℕ → ℕ → ℕ} (hf : Bound f) : Bound (fun t n => f t n+1) := by
  obtain ⟨A,a,b,hh⟩ := hf
  refine ⟨A+1,a,b,fun t n => ?_⟩
  let D := (n+1)^b
  let E := (t+1)^a
  have hd : 0<D := by dsimp [D]; positivity
  have he : 0<E := by dsimp [E]; positivity
  have hv : 0<2^(A*E)*D := Nat.mul_pos (by positivity) hd
  change f t n+1 ≤ 2^((A+1)*E)*D
  have hx := hh t n
  change f t n ≤ 2^(A*E)*D at hx
  calc
    f t n+1 ≤ (2^(A*E)*D)*2 := by omega
    _ = 2^(A*E+1)*D := by rw [pow_succ]; ac_rfl
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by rw [add_mul,one_mul]; omega))

theorem add {f g : ℕ → ℕ → ℕ} (hf : Bound f) (hg : Bound g) : Bound (fun t n => f t n+g t n) := by
  apply mono (mul (succ hf) (succ hg))
  intro t n
  change f t n+g t n ≤ (f t n+1)*(g t n+1)
  rw [Nat.add_mul, Nat.mul_add,one_mul,mul_one]
  omega

theorem pow {f : ℕ → ℕ → ℕ} (hf : Bound f) (k : ℕ) : Bound (fun t n => (f t n)^k) := by
  induction k with
  | zero => simpa using const 1
  | succ k ih => simpa only [pow_succ] using mul ih hf

theorem eval (P : Polynomial ℕ) {f : ℕ → ℕ → ℕ} (hf : Bound f) :
    Bound (fun t n => P.eval (f t n)) := by
  induction P using Polynomial.induction_on' with
  | add p q hp hq => simpa only [Polynomial.eval_add] using add hp hq
  | monomial k a => simpa only [Polynomial.eval_monomial] using mul (const a) (pow hf k)

theorem scaledExp (A B a : ℕ) : Bound (fun t _ => 2^(A*(B*(t+1))^a)) := by
  refine ⟨A*B^a,a,0,?_⟩
  intro t n
  simp [mul_pow,Nat.mul_assoc]

theorem polynomialBound (P : Polynomial ℕ) : ∃ A d : ℕ, ∀ t, P.eval t ≤ A*(t+1)^d := by
  induction P using Polynomial.induction_on' with
  | monomial k a =>
    exact ⟨a,k,fun t => by simp only [Polynomial.eval_monomial]; gcongr; omega⟩
  | add P Q hp hq =>
    obtain ⟨A,a,hP⟩ := hp
    obtain ⟨C,c,hQ⟩ := hq
    refine ⟨A+C,a+c,fun t => ?_⟩
    rw [Polynomial.eval_add]
    exact (Nat.add_le_add (hP t) (hQ t)).trans (merge_exp A C a c t)

theorem expPolynomial (P : Polynomial ℕ) : Bound (fun t _ => 2^(P.eval t)) := by
  obtain ⟨A,d,hh⟩ := polynomialBound P
  exact ⟨A,d,0,fun t n => by simp only [pow_zero,mul_one]; exact Nat.pow_le_pow_right (by decide) (hh t)⟩

theorem polyExp (P : Polynomial ℕ) (C d : ℕ) : Bound (fun t _ => 2^(C*(P.eval t+1)^d)) := by
  simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_one]
    using expPolynomial (Polynomial.C C*(P+1)^d)

end DualSepClusterLP.TimeBudget
end

/- BoundedWords -/
section
namespace DualSepClusterLP.WordSearch
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
variable {α β : Type} [Coding α] [Coding β]

theorem verifier_clock_before {ok : α × W → Bool} {out : α × W → β} (hc : Poly ok) (he : Poly out) :
    ∃ (A b : ℕ), ∀ (x : α) (w : W), ok (x,w++[true])=true →
      ∃ j : ℕ, j ≤ code w ∧ ok (x,j.bits)=true ∧ Nonempty (Turing.TM2OutputsInTime (machine hc he).tm
        (enc x) (some (enc (out (x,j.bits))))
        (2^(w.length+1)*A*((enc x).length+w.length+1)^b)) := by
  let init := start (α:=α)
  let p := program hc he
  let g : Polynomial ℕ := init.time + 2*(2*Polynomial.X+1) + 2 +
    (p.time + 2*p.sizeBound+3).comp (2*Polynomial.X+2)
  have clk (P : Polynomial ℕ) : ∃ A b : ℕ, ∀ m, P.eval m ≤ A*(m+1)^b := by
    induction P using Polynomial.induction_on' with
    | monomial k a => exact ⟨a,k,fun m => by simp only [Polynomial.eval_monomial]; gcongr; omega⟩
    | add P Q hp hq =>
      obtain ⟨A,b,hA⟩ := hp; obtain ⟨C,d,hC⟩ := hq
      refine ⟨A+C,b+d,fun m => ?_⟩
      rw [Polynomial.eval_add,add_mul]
      exact (Nat.add_le_add (hA m) (hC m)).trans (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))))
  obtain ⟨A,b,hab⟩ := clk g
  refine ⟨A,b,?_⟩; intro x w hw
  let K := code w
  have hbits : K.bits = w++[true] := bits_code w
  obtain ⟨j,t,hj,hv,ht,hr⟩ := trace hc he x K (by rwa [hbits])
  let m := (enc x).length+w.length
  have hk : K+1 ≤ 2^(w.length+1) := by
    have h := Nat.lt_size_self K
    rwa [←Nat.size_eq_bits_len,hbits,List.length_append,List.length_singleton] at h
  have hi : (enc ((x,0):α × ℕ)).length ≤ 2*m+1 := by
    change (encodePair enc Nat.bits (x,0)).length ≤ _
    simp [encodePair_length,m]
  have hs : stateSize x K ≤ 2*m+2 := by
    change (encodePair enc Nat.bits (x,K)).length ≤ _
    simp [encodePair_length,hbits,m]; omega
  have hxm : (enc x).length ≤ m := Nat.le_add_right _ _
  have h := ht.trans (Nat.add_le_add (Nat.add_le_add_right
    (Nat.add_le_add (polynomial_eval_mono init.time hxm)
       (Nat.mul_le_mul_left 2 hi)) 2)
    (Nat.mul_le_mul hk (show p.passTime (stateSize x K) ≤
      (p.time+2*p.sizeBound+3).eval (2*m+2) by
      simp only [PolyProgram.passTime,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat]
      gcongr <;> apply polynomial_eval_mono _ hs)))
  have hb : t≤ 2^(w.length+1)*g.eval m := by
    simp only [g,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_comp,Polynomial.eval_ofNat,Polynomial.eval_one]
    simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat] at h
    have hpos : 0<2^(w.length+1) := by positivity
    nlinarith
  refine ⟨j,hj,hv,⟨⟨⟨_,hr.iterate_eq⟩,?_⟩⟩⟩
  exact hb.trans (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (hab m))

end DualSepClusterLP.WordSearch
end

/- SearchSize -/
section
namespace DualSepClusterLP.SepSearch
open TimeBudget

def cap (C d t n : ℕ) := 8*(2*(2*(n+1)).bits.length+1)+C*(t+1)^d+1

theorem cap_mono (C d t : ℕ) {n m : ℕ} (hn : n ≤ m) : cap C d t n ≤ cap C d t m := by
  unfold cap
  have h := Nat.size_le_size (show 2*(n+1) ≤ 2*(m+1) by omega)
  simp only [Nat.size_eq_bits_len]
  omega

theorem cap_bound (C d : ℕ) : Bound (cap C d) := by
  let B := fun t n : ℕ => 8*(2*(2*(n+1)+1)+1)+C*(t+1)^d+1
  have hB : Bound B := add (add (mul (const _) (add (mul (const _) (add (mul (const _) (add size (const _))) (const _))) (const _)))
    (mul (const _) (TimeBudget.pow (add param (const _)) d))) (const _)
  apply mono hB
  intro t n
  have h : (2*(n+1)).bits.length ≤ 2*(n+1)+1 := OAI.MetricKMedian.Binary.NatBinary.length_le_height Nat.lt_two_pow_self.le
  unfold B cap
  omega

private theorem bits_pow (m : ℕ) (h : 0 < m) : 2^m.bits.length ≤ 2*m := by
  rw [Nat.size_eq_bits_len]
  have hh := Nat.size_pos.mpr h
  have hp : m.size-1 < m.size := by omega
  have hs := Nat.lt_size.mp hp
  nth_rw 1 [show m.size = (m.size-1)+1 by omega]
  rw [pow_succ]
  omega

theorem cap_exp_bound (C d : ℕ) : Bound (fun t n => 2^(cap C d t n+2)) := by
  have ep : Bound (fun t _ => 2^(C*(t+1)^d)) := ⟨C,d,0,by simp⟩
  apply mono (mul (mul (const 2048) ep) (TimeBudget.pow (mul (const 4) (add size (const 1))) 16))
  intro t n
  have he := bits_pow (2*(n+1)) (by omega)
  unfold cap
  rw [show 8*(2*(2*(n+1)).bits.length+1)+C*(t+1)^d+1+2 =
    11+C*(t+1)^d+(2*(n+1)).bits.length*16 by omega,pow_add,pow_add,pow_mul 2 (2*(n+1)).bits.length 16]
  have hp : (2^(2*(n+1)).bits.length)^16 ≤ (4*(n+1))^16 :=
    Nat.pow_le_pow_left (by omega) _
  exact Nat.mul_le_mul_left _ hp

end DualSepClusterLP.SepSearch
end

/- SearchTest -/
section
namespace DualSepClusterLP.SepSearch
open OAI.MetricKMedian OAI.MetricKMedian.InputParser OAI.MetricKMedian.Binary
open OAI.MetricKMedian.Binary.Automatic OAI.MetricKMedian.Binary.Automatic.Poly
open SolverWords (Word GraphWord graphWord)

def word (p : Params) := p.1.flatMap lengthPrefixedNat ++ p.2

def unpack (w : Word) : Params :=
  parse natRead (List.replicate 8 (),w.take (w.length-1))
@[fun_prop] theorem unpack_poly : Poly unpack := by
  have h : Poly (parse natRead) := ⟨parseProgram natRead natRead_poly.program natRead_rest_length⟩
  unfold unpack; fun_prop

theorem unpack_word (p : Params) (h : p.1.length=8) : unpack (word p ++ [true])=p := by
  have hh := parse_encoded natRead lengthPrefixedNat (fun i w => natRead_append i w) p.1 p.2
  simp only [h,←List.flatMap_def] at hh
  simp only [unpack,List.length_append,List.length_singleton,Nat.add_sub_cancel,List.take_left]
  exact hh

theorem word_length (C d t n : ℕ) (p : Params) (h : p.1.length=8) (hm : ∀ i∈p.1,i≤2*(n+1))
    (hb : p.2.length≤C*(t+1)^d) : (word p).length+1 ≤ cap C d t n := by
  let M := 2*(2*(n+1)).bits.length+1
  have hi (xs : List ℕ) (hx : ∀ i∈xs,i≤2*(n+1)) : (xs.flatMap lengthPrefixedNat).length ≤ xs.length*M := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hh := NatBinary.length_mono (hx x (by simp))
      have hj := ih (fun i hi => hx i (by simp [hi]))
      simp only [List.flatMap_cons,List.length_append,List.length_cons,lengthPrefixedNat,
        List.length_replicate,List.length_nil,Nat.add_mul,one_mul]
      unfold M at *; omega
  have hp := hi p.1 hm
  rw [h] at hp; change _ ≤ _ at hp
  unfold word cap
  simp only [List.length_append]
  unfold M at hp; omega

@[fun_prop] theorem nat_pow_comp {α : Type} [Coding α] {f : α→ℕ} (hf : Poly f) (d : ℕ) :
    Poly (fun x => (f x)^d) := by
  induction d with
  | zero => simpa only [pow_zero] using (Automatic.Poly.const (1:ℕ) : Poly (fun _ : α => (1:ℕ)))
  | succ d ih => simp only [pow_succ]; fun_prop

def stop (C d : ℕ) (x : Data × Word) : Bool :=
  decide (cap C d x.1.1 x.1.2.1.1.length < x.2.length)
@[fun_prop] theorem stop_poly (C d : ℕ) : Poly (stop C d) := by
  unfold stop cap
  fun_prop

def propose (c : Candidate) (x : Data × Word) : Data × List ℕ :=
  (x.1,c (x.1,unpack x.2))
@[fun_prop] theorem propose_poly {c : Candidate} (hc : Poly c) : Poly (propose c) := pair fst (comp hc (pair fst (comp unpack_poly snd)))

def ok (c : Candidate) (C d : ℕ) (x : Data × Word) : Bool :=
  if stop C d x then true else valid (propose c x)
@[fun_prop] theorem ok_poly {c : Candidate} (hc : Poly c) (C d : ℕ) : Poly (ok c C d) := by
  exact Automatic.Poly.ite (stop_poly C d) (Automatic.Poly.const true) (comp valid_poly (propose_poly hc))

def out (c : Candidate) (x : Data × Word) : Word :=
  let a := propose c x
  if valid a then true :: makeMask (a.1.2.1.1,a.2) else [false]
@[fun_prop] theorem out_poly {c : Candidate} (hc : Poly c) : Poly (out c) := by
  let put : Data × List ℕ → Word := fun a => true :: makeMask (a.1.2.1.1,a.2)
  have hu : Poly put := by unfold put; fun_prop
  exact Automatic.Poly.ite (comp valid_poly (propose_poly hc)) (comp (f:=put) (g:=propose c) hu (propose_poly hc)) (Automatic.Poly.const [false])

theorem out_yes (c : Candidate) {n : ℕ} (G : Graph n) (q : Fin n→ℚ) (t : ℕ) (w : Word)
    (h : valid (propose c (data G q t,w))=true) :
    out c (data G q t,w) = separationOutput (some (setOfIds (c (data G q t,unpack w)): Finset (Fin n))) := by
  unfold out; simp only [h,if_true]
  change true :: makeMask (List.range n,_) = true::_
  rw [makeMask_spec]; rfl

end DualSepClusterLP.SepSearch
end

/- MachineBudget -/
section
namespace DualSepClusterLP.MachineBudget
open Turing OAI.MetricKMedian.Binary

abbrev Word := List Bool
abbrev Run (M : Machine) (x y : Word) (s : ℕ) := Nonempty (TM2OutputsInTime M.tm x (some y) s)

noncomputable def factor (M : Machine) : ℕ := M.growth

theorem length {M : Machine} {x y : Word} {s : ℕ} (h : Run M x y s) :
    y.length ≤ x.length + factor M*s := by simpa only [factor,Nat.mul_comm] using M.output_length h.some

theorem weaken {M : Machine} {x y : Word} {s t : ℕ} (h : Run M x y s) (hst : s≤t) : Run M x y t := by
  obtain ⟨r⟩ := h
  exact ⟨⟨r.toEvalsTo,r.steps_le_m.trans hst⟩⟩

theorem compose {M N : Machine} {x y z : Word} {s t : ℕ} (h : Run M x y s) (j : Run N y z t) :
    Run (Compose.machine M N) x z (s+2*y.length+2+t) := by
  obtain ⟨p⟩ := h
  obtain ⟨q⟩ := j
  have hp : Trace M.step p.steps (M.initialCfg x) (M.finalCfg y) := Trace.of_iterate p.evals_in_steps
  have hq : Trace N.step q.steps (N.initialCfg y) (N.finalCfg z) := Trace.of_iterate q.evals_in_steps
  have hh := Compose.run M N hp hq
  exact ⟨⟨⟨_,hh.iterate_eq⟩,Nat.add_le_add (Nat.add_le_add_right (Nat.add_le_add_right p.steps_le_m _) _) q.steps_le_m⟩⟩

theorem program {α β : Type} {ea : α → Word} {eb : β → Word} {f : α → β}
    (P : PolyProgram ea eb f) (a : α) : Run P.machine (ea a) (eb (f a)) (P.time.eval (ea a).length) :=
  ⟨P.outputs a⟩

noncomputable def outputSize (M : Machine) (input s : ℕ) := input + factor M*s
noncomputable def thenCost (M : Machine) (input s t : ℕ) := s+2*outputSize M input s+2+t
theorem compose_le {M N : Machine} {x y z : Word} {d s t : ℕ}
    (hx : x.length ≤ d) (h : Run M x y s) (j : Run N y z t) :
    Run (Compose.machine M N) x z (thenCost M d s t) := by
  have hy : y.length ≤ outputSize M d s := (length h).trans (Nat.add_le_add_right hx _)
  apply weaken (compose h j)
  unfold thenCost
  omega

section
open TimeBudget
variable {d s j : ℕ → ℕ → ℕ} (M : Machine)

theorem outputSize_bound (hd : Bound d) (hs : Bound s) : Bound (fun t n => outputSize M (d t n) (s t n)) :=
  add hd (mul (const _) hs)

theorem thenCost_bound (hd : Bound d) (hs : Bound s) (hj : Bound j) :
    Bound (fun t n => thenCost M (d t n) (s t n) (j t n)) :=
  add (add (add hs (mul (const 2) (outputSize_bound M hd hs))) (const 2)) hj

end

end DualSepClusterLP.MachineBudget
end

/- Decision -/
section
namespace DualSepClusterLP.SepSearch
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open SolverWords (Word)
open TimeBudget

abbrev Goodness := (t n : ℕ) → Graph n → (Fin n → ℚ) → Prop
def answers (Good : Goodness) {n : ℕ} (t : ℕ) (G : Graph n) (q : Fin n → ℚ) (r : Option (Finset (Fin n))) : Prop :=
  match r with
  | some S => subsetCost G S < ∑ i∈S,(q i:ℝ)
  | none => Good t n G q

private theorem witness {n : ℕ} (c : Candidate) (C d t : ℕ) (G : Graph n) (q : Fin n→ℚ)
    (Good : Goodness) (hc : complete c C d Good) :
    ∃ w : Word, w.length ≤ cap C d t n ∧ ok c C d (data G q t,w++[true])=true ∧
      (¬Good t n G q → w.length+1 ≤ cap C d t n) := by
  classical
  by_cases hg : Good t n G q
  · let z := cap C d t n
    refine ⟨List.replicate z false,by simp [z],?_,fun h => (h hg).elim⟩
    have hs : stop C d (data G q t,List.replicate z false++[true])=true := by
      simp [stop,data,SolverWords.graphWord,z]
    simp [ok,hs]
  · obtain ⟨p,hp,hn,hl,hv⟩ := hc t n G q hg
    have hs := word_length C d t n p hp hn hl
    have hv' : valid (propose c (data G q t,word p++[true]))=true := by
      rw [propose,unpack_word p hp,valid_spec]; exact hv
    exact ⟨word p,by omega,by simp [ok,hv'],fun _ => hs⟩

noncomputable def readProgram := BooleanLists.packProgram.comp readData_poly.program

def widthBound (t k : ℕ) := (t+k+2)^2+k
theorem widthBound_bound : Bound widthBound := add (TimeBudget.pow (add (add param size) (const 2)) 2) size

theorem input_length {n : ℕ} (t : ℕ) (G : Graph n) (q : Fin n→ℚ) :
    (separationInput t G q).length ≤ widthBound t (n+(pricesBits q).length) := by
  simp [separationInput,graphInput,matrixBits,List.length_flatMap,List.map_const',widthBound]
  nlinarith

noncomputable def scan {c : Candidate} (hc : Poly c) (C d : ℕ) :=
  WordSearch.machine (ok_poly hc C d) (out_poly hc)

theorem scan_correct (c : Candidate) (hp : Poly c) (C d : ℕ) (Good : Goodness) (hc : complete c C d Good) :
    ∃ F : ℕ→ℕ→ℕ, Bound F ∧ ∀ t n (G : Graph n) (q : Fin n→ℚ),
    ∃ r : Option (Finset (Fin n)), answers Good t G q r ∧ MachineBudget.Run (scan hp C d)
      (enc (data G q t)) (enc (separationOutput r)) (F t (n+(pricesBits q).length)) := by
  obtain ⟨A,b,hA⟩ := WordSearch.verifier_clock_before (ok_poly hp C d) (out_poly hp)
  let B := fun t k => readProgram.sizeBound.eval (widthBound t k)
  let F := fun t k => 2^(cap C d t k+2)*A*(B t k+cap C d t k+1)^b
  have hB : Bound B := TimeBudget.eval _ widthBound_bound
  have hF : Bound F := mul (mul (cap_exp_bound C d) (const _)) (TimeBudget.pow (add (add hB (cap_bound C d)) (const 1)) b)
  refine ⟨F,hF,?_⟩; intro t n G q
  let x := data G q t
  let k := n+(pricesBits q).length
  have hn : n ≤ k := Nat.le_add_right _ _
  have hlen : (enc x).length ≤ B t k := by
    have hh := readProgram.length_bound (separationInput t G q)
    change (enc (readData (separationInput t G q))).length ≤ _ at hh
    rw [readData_spec] at hh
    exact hh.trans (polynomial_eval_mono _ (input_length t G q))
  obtain ⟨w,hl,hw,hshort⟩ := witness c C d t G q Good hc
  obtain ⟨j,hj,hy,run⟩ := hA x w hw
  have hcap := cap_mono C d t hn
  have hrt : 2^(w.length+1)*A*((enc x).length+w.length+1)^b ≤ F t k := by
    unfold F
    gcongr <;> omega
  have hrun := MachineBudget.weaken run hrt
  by_cases hvalid : valid (propose c (x,j.bits))=true
  · refine ⟨some (setOfIds (c (x,unpack j.bits))),?_,?_⟩
    · exact (valid_spec t G q _).mp hvalid
    · rw [←out_yes c G q t j.bits hvalid]
      exact hrun
  · refine ⟨none,?_,?_⟩
    · change Good t n G q
      by_contra hh
      have hlen' := OAI.MetricKMedian.Binary.NatBinary.length_mono hj
      rw [WordSearch.bits_code,List.length_append,List.length_singleton] at hlen'
      have hss := hshort hh
      have hstop : stop C d (x,j.bits)=false := by
        change decide (cap C d t (List.range n).length < j.bits.length) = false
        simp only [List.length_range,decide_eq_false_iff_not,not_lt]; omega
      simp [ok,hstop,hvalid] at hy
    · have he : out c (x,j.bits)=[false] := by simp [out,hvalid]
      rw [he] at hrun
      exact hrun

end DualSepClusterLP.SepSearch
end

/- Compilation -/
section
namespace DualSepClusterLP.SepSearch
open OAI.MetricKMedian.Binary OAI.MetricKMedian.Binary.Automatic
open MachineBudget TimeBudget
open SolverWords (Word)

def asAux (M : Machine) : Turing.TM2ComputableAux Bool Bool :=
  ⟨M.tm,Equiv.refl Bool,Equiv.refl Bool⟩

private theorem external_run (P : Machine) {x y : List Bool} {s : ℕ} (h : Run P x y s) :
    Nonempty (Turing.TM2OutputsInTime (asAux P).tm (x.map (asAux P).inputAlphabet.symm)
      (some (y.map (asAux P).outputAlphabet.symm)) s) := by
  have hx : x.map (asAux P).inputAlphabet.symm = x := List.map_id x
  have hy : y.map (asAux P).outputAlphabet.symm = y := List.map_id y
  rw [hx,hy]
  exact h

theorem compile (Good : Goodness) (c : Candidate) (hc : Poly c) (C d : ℕ) (h : complete c C d Good) :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (A a b : ℕ), (∀ k, Finite (M.tm.Γ k)) ∧
    ∀ t n (G : Graph n) (q : Fin n → ℚ), ∃ r : Option (Finset (Fin n)),
      Nonempty (Turing.TM2OutputsInTime M.tm ((separationInput t G q).map M.inputAlphabet.symm)
        (some ((separationOutput r).map M.outputAlphabet.symm)) (2^(A*(t+1)^a)*(n+(pricesBits q).length+1)^b)) ∧
      answers Good t G q r := by
  obtain ⟨F,hF,hscan⟩ := scan_correct c hc C d Good h
  let P := readProgram
  let T := scan hc C d
  let Q := BooleanLists.unpackProgram
  let R := Compose.machine P.machine T
  let M := Compose.machine R Q.machine
  let w := widthBound
  let a := fun t k => P.time.eval (w t k)
  let b := fun t k => thenCost P.machine (w t k) (a t k) (F t k)
  let e := fun t k => Q.time.eval (outputSize R (w t k) (b t k))
  let g := fun t k => thenCost R (w t k) (b t k) (e t k)
  have hw : Bound w := widthBound_bound
  have ha : Bound a := TimeBudget.eval _ hw
  have hb : Bound b := thenCost_bound P.machine hw ha hF
  have he : Bound e := TimeBudget.eval _ (outputSize_bound R hw hb)
  obtain ⟨K,i,j,hg⟩ := (thenCost_bound R hw hb he : Bound g)
  refine ⟨asAux M,K,i,j,fun _ => inferInstanceAs (Finite Bool),?_⟩
  intro t n G q
  let k := n+(pricesBits q).length
  let x := separationInput t G q
  obtain ⟨r,hr,hs⟩ := hscan t n G q
  have hl : x.length ≤ w t k := input_length t G q
  have h1 : Run P.machine x (enc (data G q t)) (a t k) := by
    have hy := program P x
    change Run _ x (enc (readData (separationInput t G q))) _ at hy
    rw [readData_spec] at hy
    exact weaken hy (polynomial_eval_mono _ hl)
  have h2 : Run R x (enc (separationOutput r)) (b t k) := compose_le hl h1 hs
  have hy := (length h2).trans (Nat.add_le_add_right hl _)
  have h3 : Run Q.machine (enc (separationOutput r)) (separationOutput r) (e t k) :=
    weaken (program Q (separationOutput r)) (polynomial_eval_mono Q.time hy)
  have ht : Run M x (separationOutput r) (g t k) := compose_le hl h2 h3
  exact ⟨r,external_run M (weaken ht (hg t k)),hr⟩

end DualSepClusterLP.SepSearch
end

/- LocalMachine -/
section
open DualSepClusterLP

theorem solution  :
    ∃ (M : Turing.TM2ComputableAux Bool Bool) (A a b : ℕ),
      (∀ k, Finite (M.tm.Γ k)) ∧
      ∀ (t n : ℕ) (G : Graph n) (q : Fin n → ℚ),
        ∃ result : Option (Finset (Fin n)),
          Nonempty (Turing.TM2OutputsInTime M.tm
            ((separationInput t G q).map M.inputAlphabet.symm)
            (some ((separationOutput result).map M.outputAlphabet.symm))
            (2 ^ (A * (t+1)^a) * (n+(pricesBits q).length+1)^b)) ∧
          match result with
          | some S => subsetCost G S < ∑ i ∈ S, (q i : ℝ)
          | none => SepCheck.Checks t G q := by
  exact SepSearch.compile (fun t _ G q => SepCheck.Checks t G q)
    Proposal.candidate Proposal.candP Proposal.K 12 Proposal.complete
end
